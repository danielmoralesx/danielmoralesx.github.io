library(copula)
library(cubature)
library(mvtnorm)
library(numDeriv)
library(ggplot2)
library(shiny)

set.seed(1)

# source("numeric_local_measures.R")

local_rho_emp <- function(u, v, u0, u1, v0, v1) {
  ind_inside <- u >= u0 & u <= u1 & v >= v0 & v <= v1
  u_inside <- u[ind_inside]
  v_inside <- v[ind_inside]
  
  cor(u_inside, v_inside, method = "spearman")
}

local_tau_emp <- function(u, v, u0, u1, v0, v1) {
  ind_inside <- u >= u0 & u <= u1 & v >= v0 & v <= v1
  u_inside <- u[ind_inside]
  v_inside <- v[ind_inside]
  
  cor(u_inside, v_inside, method = "kendall")
}

# source("numeric.R")

LU <- function(copula, u, theta, u0, u1, v0, v1) {
  (copula(u, v1, theta) - copula(u0, v1, theta) - 
     copula(u, v0, theta) + copula(u0, v0, theta)) / 
    (copula(u1, v1, theta) - copula(u0, v1, theta) - 
       copula(u1, v0, theta) + copula(u0, v0, theta))
}

LV <- function(copula, v, theta, u0, u1, v0, v1) {
  (copula(u1, v, theta) - copula(u0, v, theta) - 
     copula(u1, v0, theta) + copula(u0, v0, theta)) / 
    (copula(u1, v1, theta) - copula(u0, v1, theta) - 
       copula(u1, v0, theta) + copula(u0, v0, theta))
}

LC <- function(copula, u, v, theta, u0, u1, v0, v1) {
  (copula(u, v, theta) - copula(u0, v, theta) - 
     copula(u, v0, theta) + copula(u0, v0, theta)) / 
    (copula(u1, v1, theta) - copula(u0, v1, theta) - 
       copula(u1, v0, theta) + copula(u0, v0, theta))
}

local_rho <- function(copula, u0, u1, v0, v1, theta) {
  if (identical(copula, function(u, v, theta) 
    u * v + theta * u * v * (1 - u) * (1 - v))) {
      ((u1 - u0) * (v1 - v0) * theta) / 
        (3 * (1 + (1 - u1 - u0) * (1 - v1 - v0) * theta) ^ 2)
  } else {
    aux_func <- function(x) {
      u <- x[1]
      v <- x[2]
      LC(copula, u, v, theta, u0, u1, v0, v1) * 
        grad(LU, 
             x = u,
             copula = copula, theta = theta, 
             u0 = u0, u1 = u1, v0 = v0, v1 = v1) * 
        grad(LV, 
             x = v, 
             copula = copula, theta = theta, 
             u0 = u0, u1 = u1, v0 = v0, v1 = v1)
    }
    -3 + 12 * adaptIntegrate(f = aux_func,
                             lowerLimit = c(u0 ,v0),
                             upperLimit = c(u1, v1))$integral
  }
}

local_tau <- function(copula, u0, u1, v0, v1, theta) {
  if (identical(copula, function(u, v, theta)
    u * v + theta * u * v * (1 - u) * (1 - v))) {
    (2 * (u1 - u0) * (v1 - v0) * theta) /
      (9 * (1 + (1 - u1 - u0) * (1 - v1 - v0) * theta) ^ 2)
  } else {
    aux_func_int <- function(x) {
      u <- x[1]
      v <- x[2]
      aux_func_deriv <- function(x) {
        LC(copula, x[1], x[2], theta, u0, u1, v0, v1)
      }
      LC(copula, u, v, theta, u0, u1, v0, v1) * 
        hessian(aux_func_deriv, c(u, v))[1, 2]
    }
    -1 + 4 * adaptIntegrate(f = aux_func_int,
                            lowerLimit = c(u0 ,v0),
                            upperLimit = c(u1, v1))$integral
  }
}

# Copula Functions

# amh_copula1 <- function(u, v, theta) {
#   (1 - theta) / (((1 - theta) / u + theta) * 
#                    ((1 - theta) / v + theta) - theta)
# }

amh_copula <- function(u, v, theta) {
  if (u == 0 && v == 0 && theta == 1) 0
  else u * v / (1 - theta * (1 - u) * (1 - v))
}

# amh_copula3 <- function(u, v, theta) {
#   -1/theta * log(1 + exp(-(-log((exp(-theta *  u) - 1)/(exp(-theta) - 1)) + 
#                              -log((exp(-theta * v) - 1)/(exp(-theta) - 1)))) * 
#                    (exp(-theta) - 1))
# }

clayton_copula <- function(u, v, theta) {
  if (theta == 0) u * v
  else max(u ^ (-theta) + v ^ (-theta) - 1, 0, na.rm = TRUE) ^ (-1 / theta)
}

fgm_copula <- function(u, v, theta) u * v + theta * u * v * (1 - u) * (1 - v)

frank_copula <- function(u, v, theta) {
  (-1 / theta) * 
    log(1 + ((exp(-theta * u) - 1) * (exp(-theta * v) - 1)) / (exp(-theta) - 1))
}

gumbel_copula <- function(u, v, theta) {
  exp(-((-log(u)) ^ theta + (-log(v)) ^ theta) ^ (1 / theta))
}

# joe_copula <- function(u, v, theta) {
#   aux_u <- (1 - u) ^ theta
#   aux_v <- (1 - v) ^ theta
#   1 - (aux_u + aux_v - aux_u * aux_v) ^ (1 / theta)
# }
# 
# joe_copula2 <- function(u, v, theta) {
#   1 - (1 - (1 - (1 - u)^theta) * (1 - (1 - v)^theta))^(1/theta)
# }

normal_copula <- function(u, v, theta) {
  pmvnorm(lower = c(-Inf, -Inf),
          upper = c(qnorm(u), qnorm(v)),
          mean = c(0, 0),
          corr = matrix(c(1, theta, theta, 1), 2))[[1]]
}

# Copula lists
copula_list <- list(amh_copula,
                    clayton_copula,
                    fgm_copula,
                    frank_copula,
                    gumbel_copula,
                    normal_copula)

param_bnds_thr <- list(c(-1, 1),
                       c(-1, Inf),
                       c(-1, 1),
                       c(-Inf, Inf),
                       c(1, Inf),
                       c(-1, 1))

param_bnds_num <- list(c(-1, 1),
                       c(-0.95, 10),
                       c(-1, 1),
                       c(-10, 10),
                       c(1, 10),
                       c(-0.95, 1))

copula_names <- c("Ali-Mikhail-Haq Copula" = 1,
                  "Clayton Copula" = 2,
                  "Farlie-Gumbel-Morgenstern Copula" = 3,
                  "Frank Copula" = 4,
                  "Gumbel Copula" = 5,
                  "Normal Copula" = 6)

copula_latex_formula <- c(
  "$$ C(u, v) = \\dfrac{u v}{1 - \\theta (1 - u) (1 - v)} \\text{, where } \\theta \\in [-1, 1] $$",
  "$$ C(u, v) = \\text{max}(u ^ {-\\theta} + v ^ {-\\theta} - 1, 0) ^ {-1 / \\theta} \\text{, where } \\theta \\in [-1, \\infty[ $$",
  "$$ C(u, v) = u v + \\theta u v (1 - u) (1 - v) \\text{, where } \\theta \\in [-1, 1] $$",
  "$$ C(u, v) = -\\theta^{-1} \\log \\left( 1 + \\dfrac{(\\exp(-\\theta u) - 1) (\\exp(-\\theta v) - 1)}{\\exp(-\\theta) - 1} \\right) \\text{, where } \\theta \\in \\mathbb{R} $$",
  "$$ C(u, v) = \\exp(-((-\\log(u)) ^ \\theta + (-\\log(v)) ^ \\theta) ^ {1 / \\theta}) \\text{, where } \\theta \\in [1, \\infty[ $$",
  "$$ C(u, v) = \\Phi_\\theta \\left( \\Phi^{-1}(u), \\Phi^{-1}(v) \\right) \\text{, where } \\theta \\in [-1, 1] $$"
)

# Define UI for application
ui <- fluidPage(
   
  # Application title
  titlePanel("Local Copula Fit With Local Dependence Measures"),
  
  # Sidebar with inputs 
  sidebarLayout(
    sidebarPanel(
      numericInput("n", "Sample Size", 1000, min = 2),
      radioButtons("samp_copula", 
                   "Sample Copula", 
                   choices = copula_names,
                   selected = 6),
      numericInput("theta", "Copula Parameter", 0.5, step = 0.1),
      numericInput("u0", "u0", 0, min = 0, max = 1, step = 0.01),
      numericInput("u1", "u1", 0.5, min = 0, max = 1, step = 0.01),
      numericInput("v0", "v0", 0, min = 0, max = 1, step = 0.01),
      numericInput("v1", "v1", 0.5, min = 0, max = 1, step = 0.01),
      radioButtons("fit_copula", 
                   "Fit Copula", 
                   choices = copula_names,
                   selected = 5),
      radioButtons("measure", 
                   "Fit Measure",
                   choices = c("Kendall Tau", "Spearman Rho"),
                   selected = "Spearman Rho")
    ),
      
    # Plot
    mainPanel(
      tabsetPanel(
        tabPanel(
          "Data",
          column(width = 12, align = "center",
                 uiOutput("sample_copula_formula"),
                 #withMathJax(uiOutput("sample_copula_formula")),
                 plotOutput("sample_plot"),
                 tableOutput("dep_meas")
          )
        ),
        tabPanel(
          "Fit",
          column(width = 12, align = "center",
                 uiOutput("fit_copula_formula"),
                 #plotOutput("fit_copula_strp_rho")
                 plotOutput("meas_fit_plot"),
                 uiOutput("fit_theta")
          )
        )
      )
    )
  )
)

# Define server logic required
server <- function(input, output, session) {
  
  sample_copula <- reactive({
    if (input$samp_copula == "1") 
      amhCopula(input$theta)
    else if(input$samp_copula == "2")
      claytonCopula(input$theta)
    else if(input$samp_copula == "3")
      fgmCopula(input$theta)
    else if(input$samp_copula == "4")
      frankCopula(input$theta)
    else if(input$samp_copula == "5")
      gumbelCopula(input$theta)
    else if(input$samp_copula == "6")
      normalCopula(input$theta)
  })
  
  r_copula <- reactive({
    rcop <- rCopula(input$n, sample_copula())
    rcop <- data.frame(rcop)
    names(rcop) <- c("u", "v")
    rcop
  })
  
  u <- reactive(r_copula()$u)
  
  v <- reactive(r_copula()$v)
  
  output$sample_copula_formula <- renderUI({
    withMathJax(copula_latex_formula[as.numeric(input$samp_copula)])
  })
  
  output$sample_plot <- renderPlot({
    validate(
      need(input$theta >= param_bnds_thr[[as.numeric(input$samp_copula)]][1] &
             input$theta <= param_bnds_thr[[as.numeric(input$samp_copula)]][2],
           "Copula parameter out of bounds!"),
      need(input$u0 >= 0 & input$u0 <= 1, "u0 must be 0 <= u0 <= 1"),
      need(input$u1 >= 0 & input$u1 <= 1, "u1 must be 0 <= u1 <= 1"),
      need(input$u0 < input$u1, "u1 must be greater than u0"),
      need(input$v0 >= 0 & input$v0 <= 1, "v0 must be 0 <= v0 <= 1"),
      need(input$v1 >= 0 & input$v1 <= 1, "v1 must be 0 <= v1 <= 1"),
      need(input$v0 < input$v1, "v1 must be greater than v0")
    )
    ggplot(r_copula(), aes(x = u, y = v)) +
      annotate("rect", 
               xmin = input$u0, xmax = input$u1, 
               ymin = input$v0, ymax = input$v1, 
               alpha = 0.2, fill = "red") +
      geom_point() +
      geom_hline(yintercept = 0) +
      geom_vline(xintercept = 0) +
      geom_hline(yintercept = 1) +
      geom_vline(xintercept = 1) +
      theme_bw() +
      labs(title = "Sample with selected subarea") +
      xlab("u") +
      ylab("v") +
      coord_fixed()
  })
  
  samp_emp_tau <- reactive({
    local_tau_emp(u(), v(), input$u0, input$u1, input$v0, input$v1)
  })
  
  samp_emp_rho <- reactive({
    local_rho_emp(u(), v(), input$u0, input$u1, input$v0, input$v1)
  })
  
  output$dep_meas <- renderTable({
    validate(
      need(input$theta >= param_bnds_thr[[as.numeric(input$samp_copula)]][1] &
             input$theta <= param_bnds_thr[[as.numeric(input$samp_copula)]][2],
           "Copula parameter out of bounds!"),
      need(input$u0 >= 0 & input$u0 <= 1, "u0 must be 0 <= u0 <= 1"),
      need(input$u1 >= 0 & input$u1 <= 1, "u1 must be 0 <= u1 <= 1"),
      need(input$u0 < input$u1, "u1 must be greater than u0"),
      need(input$v0 >= 0 & input$v0 <= 1, "v0 must be 0 <= v0 <= 1"),
      need(input$v1 >= 0 & input$v1 <= 1, "v1 must be 0 <= v1 <= 1"),
      need(input$v0 < input$v1, "v1 must be greater than v0")
    )
    data.frame(
      "Global Empiric" = c(cor(u(), v(), method = "kendall"),
                           cor(u(), v(), method = "spearman")),
      "Global Analytic" = c(copula::tau(sample_copula()), 
                            copula::rho(sample_copula())),
      "Local Empiric" = c(samp_emp_tau(), samp_emp_rho()),
      "Local Numeric" = c(
        local_tau(copula_list[[as.numeric(input$samp_copula)]],
                  input$u0, input$u1, input$v0, input$v1, input$theta), 
        local_rho(copula_list[[as.numeric(input$samp_copula)]],
                  input$u0, input$u1, input$v0, input$v1, input$theta)
      ), 
      row.names = c("Kendall Tau", "Spearman Rho"),
      check.names = FALSE
    )
  }, rownames = TRUE)
  
  fit_copula <- reactive({
    copula_list[[as.numeric(input$fit_copula)]]
  })
  
  # output$fit_copula_strp_rho <- renderPlot({
  #   
  # })
  
  output$fit_copula_formula <- renderUI({
    withMathJax(copula_latex_formula[as.numeric(input$fit_copula)])
  })
  
  theta_disc <- reactive({
    seq(param_bnds_num[[as.numeric(input$fit_copula)]][1],
        param_bnds_num[[as.numeric(input$fit_copula)]][2],
        length.out = 11)
  })
  
  loc_meas_disc <- reactive({
    if (input$measure == "Kendall Tau") {
      vapply(theta_disc(), function(theta) {
        local_tau(fit_copula(), input$u0, input$u1, input$v0, input$v1, theta)
      }, numeric(1))
    } else if (input$measure == "Spearman Rho") {
      vapply(theta_disc(), function(theta) {
        local_rho(fit_copula(), input$u0, input$u1, input$v0, input$v1, theta)
      }, numeric(1))
    }
  })
  
  output$meas_fit_plot <- renderPlot({
    if (input$measure == "Kendall Tau") {
      y_interc <- samp_emp_tau()
      y_lab <- "Local Kendall Tau"
    } else if (input$measure == "Spearman Rho") {
      y_interc <- samp_emp_rho()
      y_lab <- "Local Spearman Rho"
    }
    ggplot(data.frame(theta_disc = theta_disc(), 
                      loc_meas_disc = loc_meas_disc()),
           aes(x = theta_disc, y = loc_meas_disc)) +
      geom_line() +
      geom_hline(yintercept = y_interc, color = "red") +
      theme_bw() +
      xlab("Fit Copula Parameter") +
      ylab(y_lab)
  })

  output$fit_theta <- renderUI({
    if (input$measure == "Kendall Tau") {
      validate(
        need(min(loc_meas_disc()) <= samp_emp_tau() && 
               max(loc_meas_disc()) >= samp_emp_tau(),
             "Cannot fit with selected copula.")
      )
      paste("Fitted theta =", 
                        as.character(
        uniroot(function(x) local_tau(fit_copula(), 
                                      input$u0, 
                                      input$u1, 
                                      input$v0, 
                                      input$v1, 
                                      x) - samp_emp_rho(),
                param_bnds_num[[as.numeric(input$fit_copula)]])$root
      ))
    } else if (input$measure == "Spearman Rho") {
      validate(
        need(min(loc_meas_disc()) <= samp_emp_rho() && 
               max(loc_meas_disc()) >= samp_emp_rho(),
             "Cannot fit with selected copula.")
      )
      paste("Fitted theta =", as.character(
        uniroot(function(x) local_rho(fit_copula(), 
                                      input$u0, 
                                      input$u1, 
                                      input$v0, 
                                      input$v1, 
                                      x) - samp_emp_rho(),
                param_bnds_num[[as.numeric(input$fit_copula)]])$root
      ))
    }
  })
}

# Run the application 
shinyApp(ui = ui, server = server)
