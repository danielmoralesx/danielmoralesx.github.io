source("kahale_volatility.R")

## Dados ----

spot <- 590
maturity <- c(.175, .425, .695, .94, 1, 1.5, 2, 3, 4, 5)
strike <- c(.85, .9, .95, 1, 1.05, 1.1, 1.15, 1.2, 1.3, 1.4) * spot
rate <- .06
divy <- .0262
vol <- matrix(
  c(0.190, 0.168, 0.133, 0.113, 0.102, 0.097, 0.120, 0.142, 0.169, 0.200,
    0.177, 0.155, 0.138, 0.125, 0.109, 0.103, 0.100, 0.114, 0.130, 0.150,
    0.172, 0.157, 0.144, 0.133, 0.118, 0.104, 0.100, 0.101, 0.108, 0.124,
    0.171, 0.159, 0.149, 0.137, 0.127, 0.113, 0.106, 0.103, 0.100, 0.110,
    0.171, 0.159, 0.150, 0.138, 0.128, 0.115, 0.107, 0.103, 0.099, 0.108,
    0.169, 0.160, 0.151, 0.142, 0.133, 0.124, 0.119, 0.113, 0.107, 0.102,
    0.169, 0.161, 0.153, 0.145, 0.137, 0.130, 0.126, 0.119, 0.115, 0.111,
    0.168, 0.161, 0.155, 0.149, 0.143, 0.137, 0.133, 0.128, 0.124, 0.123,
    0.168, 0.162, 0.157, 0.152, 0.148, 0.143, 0.139, 0.135, 0.130, 0.128,
    0.168, 0.164, 0.159, 0.154, 0.151, 0.148, 0.144, 0.140, 0.136, 0.132),
  10, 10, byrow = TRUE)
premium <- matrix(mapply(
  BlackScholCall,
  spot = spot,
  strike = rep(strike, each = length(strike)),
  rate = rate,
  vol = as.numeric(vol),
  maturity = rep(maturity, length(maturity)),
  divy = divy
), nrow = length(maturity), ncol = length(strike))

impvolvalid <- matrix(mapply(
  ImpVolCall,
  premium = as.numeric(premium),
  spot = spot,
  strike = rep(strike, each = length(strike)),
  rate = rate,
  maturity = rep(maturity, length(maturity)),
  divy = divy
), nrow = length(maturity), ncol = length(strike))

## Plot ----

nmaturity <- length(maturity)
SnPlist_fSabC1 <- Kahale_list_fSab(
  premium,
  matrix(rep(strike, nmaturity), nmaturity, 10, byrow = TRUE),
  rep(spot, nmaturity),
  maturity,
  "C1"
)
SnPlist_fSabC2 <- Kahale_list_fSab(
  premium,
  matrix(rep(strike, nmaturity), nmaturity, 10, byrow = TRUE),
  rep(spot, nmaturity),
  maturity,
  "C2"
)

PlotSupPlotly(maturity,
              t(matrix(rep(strike, nmaturity), nmaturity, 10, byrow = TRUE)),
              rep(spot, nmaturity),
              rep(rate, nmaturity),
              rep(divy, nmaturity),
              SnPlist_fSabC1,
              type = "premium")
PlotSupPlotly(maturity,
              t(matrix(rep(strike, nmaturity), nmaturity, 10, byrow = TRUE)),
              rep(spot, nmaturity),
              rep(rate, nmaturity),
              rep(divy, nmaturity),
              SnPlist_fSabC1,
              type = "volatility")
PlotSupPlotly(maturity,
              t(matrix(rep(strike, nmaturity), nmaturity, 10, byrow = TRUE)),
              rep(spot, nmaturity),
              rep(rate, nmaturity),
              rep(divy, nmaturity),
              SnPlist_fSabC2,
              type = "premium")
PlotSupPlotly(maturity,
              t(matrix(rep(strike, nmaturity), nmaturity, 10, byrow = TRUE)),
              rep(spot, nmaturity),
              rep(rate, nmaturity),
              rep(divy, nmaturity),
              SnPlist_fSabC2,
              type = "volatility")