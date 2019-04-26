library(nleqslv)
library(ggplot2)
library(plotly)

## Black Scholes ----
BlackScholCall <- function(spot, strike, rate, vol, maturity, divy){
  forward <- spot * exp((rate - divy) * maturity)
  sigma <- vol * sqrt(maturity)
  d1 <- log(forward / strike) / sigma + sigma / 2
  d2 <- d1 - sigma
  exp(-rate * maturity) * (forward * pnorm(d1) - strike * pnorm(d2))
}

ImpVolCall <- function(premium, spot, strike, rate, maturity, divy){
  uniroot(
    function(x) BlackScholCall(spot, strike, rate, x, maturity, divy) - premium, 
    c(-5, 5),
    tol = .Machine$double.eps ^ 0.5
  )$root
}

## Ramos da função interpoladora e suas derivadas ----
cfSab <- function(k, fSab){
  f     <- as.numeric(fSab[1])
  Sigma <- as.numeric(fSab[2])
  a     <- as.numeric(fSab[3])
  b     <- as.numeric(fSab[4])
  
  #if(any(c(k, f, Sigma) < 0)) stop("Argumentos k, f, Sigma devem ser não-negativos.")
  
  d1 <- (log(f/k) + .5 * Sigma^2) / Sigma
  d2 <- d1 - Sigma
  ifelse(is.finite(k), f*pnorm(d1) - k*pnorm(d2) + a*k + b, b) ######################################
}

c.fSab <- function(k, fSab){
  f     <- as.numeric(fSab[1])
  Sigma <- as.numeric(fSab[2])
  a     <- as.numeric(fSab[3])
  b     <- as.numeric(fSab[4])
  
  #if(any(c(k, f, Sigma) < 0)) stop("Argumentos k, f, Sigma devem ser não-negativos.")
  
  -pnorm((log(f/k) - .5 * Sigma^2) / Sigma) + a
}

c..fSab <- function(k, fSab){
  f     <- as.numeric(fSab[1])
  Sigma <- as.numeric(fSab[2])
  a     <- as.numeric(fSab[3])
  b     <- as.numeric(fSab[4])
  
  #if(any(c(k, f, Sigma) < 0)) stop("Argumentos k, f, Sigma devem ser não-negativos.")
  
  ifelse(k == 0, 0, dnorm((log(f/k) - .5 * Sigma^2) / Sigma) / (k * Sigma))
}

## Ramos k -> 0 e k -> Inf C1 ----

f0Inf <- function(Sigma, k, c.) k*exp(Sigma*qnorm(-c.) + .5*Sigma^2)

k0C1ObjFun <- function(Sigma, S, k, c, c.){
  f <- f0Inf(Sigma, k, c.)
  d1 <- log(f/k)/Sigma + .5*Sigma
  f*(pnorm(d1) - 1) + k*c. + S - c
}

fSab0 <- function(S, k, c, c.) {
  Sright <- 5
  if(k0C1ObjFun(Sright, S, k, c, c.) < 0){
    while(k0C1ObjFun(Sright, S, k, c, c.) < 0 & Sright < 10) Sright <- Sright + .05
  }
  sol <- uniroot(k0C1ObjFun, c(1e-12, Sright), 
                 S=S, k=k, c=c, c.=c., tol = .Machine$double.eps)
  Sigma <- sol$root
  f <- f0Inf(Sigma, k, c.)
  c(f, Sigma, 0, S-f)
}

kInfC1ObjFun <- function(Sigma, S, k, c, c.){
  f <- f0Inf(Sigma, k, c.)
  d1 <- (log(f/k) + .5*Sigma^2) / Sigma
  f*pnorm(d1) + k*c. - c
}

fSabInf <- function(S, k, c, c.) {
  Sright <- 5
  if(k0C1ObjFun(Sright, S, k, c, c.) < 0){
    while(k0C1ObjFun(Sright, S, k, c, c.) < 0 & Sright < 10) Sright <- Sright + .05
  }
  sol <- uniroot(kInfC1ObjFun, c(1e-12, Sright), 
                 S=S, k=k, c=c, c.=c., tol = .Machine$double.eps)
  Sigma <- sol$root
  c(f0Inf(Sigma, k, c.), Sigma, 0, 0)
}

## Funções Objetivo para resolver os sistemas ----

ObjFunC1 <- function(fSab, kcc.){
  
  k0 <- kcc.[1]
  k1 <- kcc.[2]
  c0 <- kcc.[3]
  c1 <- kcc.[4]
  c.0 <- kcc.[5]
  c.1 <- kcc.[6]
  
  f     <- fSab[1]
  Sigma <- fSab[2]
  a     <- fSab[3]
  b     <- fSab[4]
  
  d10 <- (log(f/k0) + .5 * Sigma^2) / Sigma
  d20 <- d10 - Sigma
  d11 <- (log(f/k1) + .5 * Sigma^2) / Sigma
  d21 <- d11 - Sigma
  
  Nd10 <- pnorm(d10)
  Nd11 <- pnorm(d11)
  Nd20 <- pnorm(d20)
  Nd21 <- pnorm(d21)
  
  if(is.finite(k1)){
    funeval <- c(f*Nd10 - k0*Nd20 + a*k0 + b - c0,
                 f*Nd11 - k1*Nd21 + a*k1 + b - c1,
                 -Nd20 + a - c.0,
                 -Nd21 + a - c.1)
  }
  else{
    funeval <- c(f*Nd10 - k0*Nd20 + a*k0 + b - c0,
                 b - c1,
                 -Nd20 + a - c.0,
                 -Nd21 + a - c.1)
  }
  
  funeval
}

JacFunC1 <- function(fSab, kcc.){
  
  k0 <- kcc.[1]
  k1 <- kcc.[2]
  
  f     <- fSab[1]
  Sigma <- fSab[2]
  a     <- fSab[3]
  b     <- fSab[4]
  
  d10 <- (log(f/k0) + .5 * Sigma^2) / Sigma
  d20 <- d10 - Sigma
  d11 <- (log(f/k1) + .5 * Sigma^2) / Sigma
  d21 <- d11 - Sigma
  
  Nd10 <- pnorm(d10)
  Nd11 <- pnorm(d11)
  #Nd20 <- pnorm(d20)
  #Nd21 <- pnorm(d21)
  
  jaceval <- matrix(c(Nd10 + dnorm(d10)/Sigma - k0*dnorm(d20)/(Sigma*f), f*dnorm(d10) * (-log(f/k0)/Sigma^2 + .5) - k0*dnorm(d20)*(-log(f/k0)/Sigma^2 - .5), k0, 1,
                      Nd11 + dnorm(d11)/Sigma - k1*dnorm(d21)/(Sigma*f), f*dnorm(d11) * (-log(f/k1)/Sigma^2 + .5) - k1*dnorm(d21)*(-log(f/k1)/Sigma^2 - .5), k1, 1,
                      -dnorm(d20)/(Sigma*f)                            , -dnorm(d20) * (-log(f/k0)/Sigma^2 - .5)                                           , 1 , 0,
                      -dnorm(d21)/(Sigma*f)                            , -dnorm(d21) * (-log(f/k1)/Sigma^2 - .5)                                           , 1 , 0), 4, 4, byrow = TRUE)
  if(k0 == 0) jaceval[c(1, 3), 2] <- 0
  if(!is.finite(k1)) jaceval[c(2, 4), 1:2] <- 0
  
  jaceval
}

ObjFunC2it <- function(fSab12, k, c, c.){
  fSab1 <- fSab12[1:4]
  fSab2 <- fSab12[5:8]
  
  eval <- c(cfSab(k[1], fSab1) - c[1],
            c.fSab(k[1], fSab1) - c.[1],
            cfSab(k[2], fSab1) - c[2],
            cfSab(k[2], fSab2) - c[2],
            c.fSab(k[2], fSab1) - c.fSab(k[2], fSab2),
            c..fSab(k[2], fSab1) - c..fSab(k[2], fSab2),
            cfSab(k[3], fSab2) - c[3],
            c.fSab(k[3], fSab2) - c.[2])
  eval
}

ObjFunC2 <- function(nintfSab, c, k, S){
  n <- length(k)
  if(n > 0){
    c <- sort(c, TRUE)
    k <- sort(k)
  }
  l <- (c[2:(n+2)] - c[1:(n+1)]) / (k[2:(n+2)] - k[1:(n+1)])
  #if(!all(c(!is.unsorted(l, strictly = TRUE), -1 < l[1], l[n+1]) <= 0))
  #  stop("Sequência não atende condições de convexidade.")
  
  # Restrições nos limites
  eval <- c(cfSab(0, nintfSab[1:4]) - S,
            c.fSab(0, nintfSab[1:4]) + 1,
            cfSab(Inf, nintfSab[(4*n+1):(4*(n+1))]),
            c.fSab(Inf, nintfSab[(4*n+1):(4*(n+1))]))
  # Restrições em cada strike fornecido
  if(n > 0)
    for(i in 1:n){
      eval <- c(eval,
                cfSab(k[i], nintfSab[(4*i - 3):(4*i)]) - c[i],
                cfSab(k[i], nintfSab[(4*i + 1):(4*(i+1))]) - c[i],
                c.fSab(k[i], nintfSab[(4*i - 3):(4*i)]) - c.fSab(k[i], nintfSab[(4*i + 1):(4*(i+1))]),
                c..fSab(k[i], nintfSab[(4*i - 3):(4*i)]) - c..fSab(k[i], nintfSab[(4*i + 1):(4*(i+1))]))
    }
  eval
}

## Funções de interpolação ----

# Escolha de x0 direto na função, idealmente usuário não teria que se preocupar com isso.
KahaleInterpC1 <- function(c, k, S, c. = NULL, shwargs = FALSE, shweqsols = FALSE, checkarb = TRUE){
  if(any(c(c, k, S) <= 0)) stop("Dados fornecidos nao sao estritamente positivos.")
  
  n <- length(k)
  if(checkarb) c <- c(S, sort(c, TRUE), 0)
  else c <- c(S, c, 0)
  if(checkarb) k <- c(0, sort(k), Inf)
  else k <- c(0, k, Inf)
  l <- (c[2:(n+2)] - c[1:(n+1)]) / (k[2:(n+2)] - k[1:(n+1)])
  if(is.null(c.)) c. <- c(-1, (l[1:n] + l[2:(n+1)])/2, 0)
  
  if(shwargs) print(list(c = c, k = k, n = n, l = l, c. = c.))
  
  if(checkarb)
    if(!all(c(!is.unsorted(l, strictly = TRUE), -1 < l[1], l[n+1] <= 0)))
      stop("Sequencia nao atende condicoes de convexidade.")
  
  scale <- 10^(nchar(round(S)) - 1)
  c <- c/scale
  k <- k/scale
  S <- S/scale
  
  nx0 <- 20
  cvg <- rep(FALSE, n-1)
  seqfSab <- data.frame()
  
  seqfSab <- rbind(fSab0(S, k[2], c[2], c.[2]), seqfSab)
  if (n >= 2) {
    for(i in 2:n){
      kcc. <- c(k[i:(i+1)], c[i:(i+1)], c.[i:(i+1)])
      x0 <- cbind(rep(S, nx0 + 5), c(seq(.01, 1, length.out = nx0),
                                     5e-5, 1e-4, 5e-4, 1e-3, 5e-3), 
                  rep(0, nx0 + 5), rep(0, nx0 + 5))
      sol <- searchZeros(x0, ObjFunC1, jac = JacFunC1, kcc. = kcc.,
                         control = list(allowSingular = TRUE, maxit = 10000, 
                                        xtol = .Machine$double.eps, ftol = 1e-12))
      cvg[i-1] <- length(sol$idxcvg) > 0
      fSab <- sol$x[1, ]
      seqfSab <- rbind(seqfSab, fSab)
      
      if(shweqsols) {
        cat("Intervalo", i, "\n")
        print(sol)
      }
    }
  }
  seqfSab <- rbind(seqfSab, fSabInf(S, k[n+1], c[n+1], c.[n+1]))
  
  names(seqfSab) <- c("f", "Sigma", "a", "b")
  seqfSab[, c(1, 4)] <- seqfSab[, c(1, 4)] * scale
  if(all(cvg)) {
    print("Interpolacao C1 concluida com sucesso.")
    return(seqfSab)
  }
  else {
    print("Falha na interpolacao.")
    return(NULL) 
  }
}

KahaleInterpC2it <- function(c, k, S, it, shwargs = FALSE, shweqsols = FALSE){
  if(any(c(c, k, S) <= 0)) stop("Dados fornecidos nao sao estritamente positivos.")
  
  n <- length(k)
  cvg <- matrix(rep(FALSE, n * it), it, n)
  c <- c(S, sort(c, TRUE), 0) 
  k <- c(0, sort(k), Inf)
  l <- (c[2:(n+2)] - c[1:(n+1)]) / (k[2:(n+2)] - k[1:(n+1)])
  c. <- c(-1, .5*(l[1:n] + l[2:(n+1)]), 0)
  gama <- c.
  
  if(!all(c(!is.unsorted(l, strictly = TRUE), -1 < l[1], l[n+1] <= 0)))
    stop("Sequencia nao atende condicoes de convexidade.")
  
  if(shwargs) print(list(c = c, k = k, n = n, l = l, c. = c.))
  C2err <- mat.or.vec(n, 1) + 1
  
  scale <- 10^(nchar(round(S)) - 1)
  c <- c/scale
  k <- k/scale
  S <- S/scale
  
  nx0 <- 9
  zers <- rep(0, nx0)
  SS <- rep(S, nx0)
  volS <- seq(.1, .5, length.out = sqrt(nx0))
  x0 <- cbind(SS, rep(volS, sqrt(nx0)), zers, zers, SS, rep(volS, each = sqrt(nx0)), zers, zers)
  
  if(it >= 1){
    for(i in 1:it){
      for(j in 1:n){
        sol <- searchZeros(x0, ObjFunC2it,
                           k = k[j:(j+2)], c = c[j:(j+2)], c. = c.[c(j, j+2)], 
                           control = list(allowSingular = TRUE, maxit = 5000,
                                          xtol = .Machine$double.eps, ftol = 1e-12))
        cvg[i, j] <- length(sol$idxcvg) > 0 
        if(shweqsols){
          cat("Iteracao", i, "Strike", j, "\n")
          print(sol)
        }
        gama[j+1] <- c.fSab(k[j+1], sol$x[1, 1:4])
      }
      c. <- gama
      if(all(cvg[i, ])) cat("Sucesso na iteracao", i, "\n", "\n")
      else cat("Falha na iteracao", i, "\n", "\n")
      
      # Mostrar novo vetor c. e diferenças em c.. -> e <-
      
      #print(c.)
      #for(ii in 1:n){
      #  print(abs(c..fSab(k[ii], seqfSab[ii, ]) - c..fSab(k[ii], seqfSab[ii+1, ])))
      #  #C2err[ii] <- abs(c..fSab(k[ii], ) - c..fSab(k[ii], ))
      #}
    }
  }
  seqfSab <- KahaleInterpC1(c[2:(n+1)], k[2:(n+1)], S, c., shwargs = shwargs, shweqsols = shweqsols)
  seqfSab[, c(1, 4)] <- seqfSab[, c(1, 4)] * scale
  seqfSab
}

KahaleInterpC2 <- function(c, k, S, shwargs = FALSE, shweqsols = FALSE){
  if(any(c(c, k, S) <= 0)) stop("Dados fornecidos nao sao estritamente positivos.")
  
  n <- length(k)
  c <- sort(c, TRUE)
  k <- sort(k)
  l <- (c[2:(n+2)] - c[1:(n+1)]) / (k[2:(n+2)] - k[1:(n+1)])
  
  if(shwargs) print(list(c = c, k = k, n = n, l = l))
  
  #if(!all(c(!is.unsorted(l, strictly = TRUE), -1 < l[1], l[n+1] <= 0)))
  #  stop("Sequência não atende condições de convexidade.")
  
  scale <- 10^(nchar(round(S)) - 1)
  c <- c/scale
  k <- k/scale
  S <- S/scale
  
  #nx0 <- 3
  #SSS <- rep(SS, nx0)
  x0 <- matrix(
    c(rep(c(S, .1, 0, 0), n+1),
      rep(c(S, .3, 0, 0), n+1),
      rep(c(S, .5, 0, 0), n+1)), 3, 4*(n+1), byrow = TRUE
  )
  
  sol <- suppressWarnings(
    searchZeros(x0, ObjFunC2, c = c, k = k, S = S, 
                control = list(allowSingular = TRUE, maxit = 20000, 
                               xtol = .Machine$double.eps, ftol = 1e-10)))
  print(sol$idxcvg)
  seqfSab <- matrix(sol$x[1, ], n+1, 4, byrow = TRUE)
  seqfSab[, c(1, 4)] <- seqfSab[, c(1, 4)] * scale
  seqfSab <- as.data.frame(seqfSab)
  names(seqfSab) <- c("f", "Sigma", "a", "b")
  seqfSab
}

## Funções de gráfico ----

PlotInterpD <- function(c, k, S, seqfSab, deriv = 1, dens = 1000) {
  
  n <- length(k)
  c <- c(S, sort(c, TRUE), 0)
  k <- c(0, sort(k), Inf)
  kplot <- c()
  cplot <- c()
  
  for(i in 1:n){
    kploti <- seq(k[i], k[i+1], length.out = dens)
    kplot <- c(kplot, kploti)
  }
  kplot <- c(kplot, seq(k[n+1], (k[n+1] + 1) * 2, length.out = dens))
  
  if(deriv == 0){
    for(i in 1:(n+1)){
      cplot <- c(cplot, cfSab(kplot[(dens*(i-1)+1):(dens*i)], seqfSab[i, ]))
      ylabel <- "Call"
    }
    
  } else if(deriv == 1) {
    for(i in 1:(n+1)){
      cplot <- c(cplot, c.fSab(kplot[(dens*(i-1)+1):(dens*i)], seqfSab[i, ]))
      ylabel <- "Call'"
    }
  } else if(deriv == 2) {
    for(i in 1:(n+1)){
      cplot <- c(cplot, c..fSab(kplot[(dens*(i-1)+1):(dens*i)], seqfSab[i, ]))
      ylabel <- "Call''"
    }
  } else stop("Valor de deriv não aceitável.")
  plot(kplot, cplot, type = "l", xlab = "Strike", ylab = ylabel)
  grid()
}

PlotInterpD.CE <- function(c, k, S, seqfSab, deriv = 1, dens = 1000) {
  
  n <- length(k)
  c <- c(S, sort(c, TRUE), 0)
  k <- c(0, sort(k), Inf)
  kplot <- c()
  cplot <- c()
  
  kplot <- seq(2 * k[2] - k[3], k[2], length.out = dens)
  for(i in 2:n){
    kploti <- seq(k[i], k[i+1], length.out = dens)
    kplot <- c(kplot, kploti)
  }
  kplot <- c(kplot, seq(k[n+1], 2 * k[n+1] - k[n], length.out = dens))
  
  if(deriv == 0){
    for(i in 1:(n+1)){
      cplot <- c(cplot, cfSab(kplot[(dens*(i-1)+1):(dens*i)], seqfSab[i, ]))
      ylabel <- "Call"
    }
    
  } else if(deriv == 1) {
    for(i in 1:(n+1)){
      cplot <- c(cplot, c.fSab(kplot[(dens*(i-1)+1):(dens*i)], seqfSab[i, ]))
      ylabel <- "Call'"
    }
  } else if(deriv == 2) {
    for(i in 1:(n+1)){
      cplot <- c(cplot, c..fSab(kplot[(dens*(i-1)+1):(dens*i)], seqfSab[i, ]))
      ylabel <- "Call''"
    }
  } else stop("Valor de deriv não aceitável.")
  plot(kplot, cplot, type = "l", xlab = "Strike", ylab = ylabel)
  grid()
}

PlotInterpD.GL <- function(c, k, S, seqfSab, deriv = 1, dens = 1000) {
  
  n <- length(k)
  c <- c(S, sort(c, TRUE), 0)
  k <- c(0, sort(k), Inf)
  kplot <- c()
  cplot <- c()
  
  kplot <- seq(2 * k[2] - k[3], k[2], length.out = dens)
  for(i in 2:n){
    kploti <- seq(k[i], k[i+1], length.out = dens)
    kplot <- c(kplot, kploti)
  }
  kplot <- c(kplot, seq(k[n+1], 2 * k[n+1] - k[n], length.out = dens))
  
  if(deriv == 0){
    for(i in 1:(n+1)){
      cplot <- c(cplot, cfSab(kplot[(dens*(i-1)+1):(dens*i)], seqfSab[i, ]))
      ylabel <- "Call"
    }
    
  } else if(deriv == 1) {
    for(i in 1:(n+1)){
      cplot <- c(cplot, c.fSab(kplot[(dens*(i-1)+1):(dens*i)], seqfSab[i, ]))
      ylabel <- "Call'"
    }
  } else if(deriv == 2) {
    for(i in 1:(n+1)){
      cplot <- c(cplot, c..fSab(kplot[(dens*(i-1)+1):(dens*i)], seqfSab[i, ]))
      ylabel <- "Call''"
    }
  } else stop("Valor de deriv não aceitável.")
  #plot(kplot, cplot, type = "l", xlab = "Strike", ylab = ylabel)
  graf <- ggplot(data.frame(kplot, cplot), aes(x = kplot, y = cplot)) +
    xlab("Strike") +
    ylab(ylabel) +
    geom_line() +
    geom_vline(data = data.frame(k[2:(n+1)]),
               xintercept = k[2:(n+1)], color = "salmon") +
    theme_bw() +
    theme(legend.position="none")
  graf
}

## Funções de superfície ----
Kahale_list_fSab <- function(cmat, kmat, S, tvec, interp_type){
  nt <- length(tvec)
  fSab <- vector("list", nt)
  for(ti in 1:nt){
    if(interp_type == "C1")
      fSab[[ti]] <- suppressWarnings(
        KahaleInterpC1(cmat[ti, ], kmat[ti, ], S[ti])
      )
    else if(interp_type == "C2")
      fSab[[ti]] <- KahaleInterpC2(cmat[ti, ], kmat[ti, ], S[ti])
  }
  fSab
}

KahaleSup <- function(t, k, tvec, kmat, fSab){
  itl <- findInterval(t, tvec)
  itu <- length(tvec) - findInterval(-t, -rev(tvec)) + 1
  ikutu <- findInterval(k, sort(kmat[, itu])) + 1
  ikutl <- findInterval(k, sort(kmat[, itl])) + 1
  
  ctu <- cfSab(k, fSab[[itu]][ikutu, ])
  ctl <- cfSab(k, fSab[[itl]][ikutl, ])
  
  if(itl < itu){
    wu <- (t - tvec[itl])/(tvec[itu] - tvec[itl])
    wl <- 1 - wu
    wl * ctl + wu * ctu
  }
  else ctu
}

PlotSupPlotly <- function(t, k, S, r, d, fSab, 
                          dens = 2000, type = "premium"){
  sgraf <- rep(S, each = dens)
  rgraf <- rep(r, each = dens)
  dgraf <- rep(d, each = dens)
  tgraf <- rep(t, each = dens)
  kgraf <- mat.or.vec(dens * length(t), 1)
  for (i in 1:length(t)) {
    kgraf[(dens * (i-1) + 1):(dens * i)] <- seq((1-(i/2-1/2)/100) * min(k[, i]), 
                                                (1+(i/2-1/2)/100) * max(k[, i]), 
                                                length.out = dens)
  }
  cgraf <- mat.or.vec(dens * length(t), 1)
  volgraf <- cgraf
  if(type == "volatility"){
    for(i in 1:(dens * length(t))){
      cgraf[i] <- KahaleSup(tgraf[i], kgraf[i], t, k, fSab)
      volgraf[i] <- ImpVolCall(cgraf[i], sgraf[i], kgraf[i],
                               rgraf[i], tgraf[i], dgraf[i])
    }
    plot_ly(data.frame(Strike = kgraf, Maturity = tgraf, Volatility = volgraf),
            x = ~Strike,
            y = ~Maturity,
            z = ~Volatility,
            type = 'scatter3d',
            mode = 'markers',
            marker = list(size = 1))
  } else if(type == "premium"){
    for(i in 1:(dens * length(t))){
      cgraf[i] <- KahaleSup(tgraf[i], kgraf[i], t, k, fSab)
    }
    surf_data <<- data.frame(sgraf, tgraf, kgraf, cgraf, volgraf, rgraf, dgraf)
    plot_ly(data.frame(Strike = kgraf, Maturity = tgraf, Premium = cgraf),
            x = ~Strike,
            y = ~Maturity,
            z = ~Premium,
            type = 'scatter3d',
            mode = 'markers',
            marker = list(size = 1))
  }
}
