## Gráfico Didático
source("kahale_volatility.R")

c <- c(6, 5, 4, 3)
k <- c(5, 7, 10, 15)
S <- 10
seqfSab <- KahaleInterpC1(c, k, S, NULL, TRUE)
seqfSab
PlotInterpD(c, k, S, seqfSab, 0)
PlotInterpD(c, k, S, seqfSab, 1)
PlotInterpD(c, k, S, seqfSab, 2)

dens <- 1000
n <- length(k)
c <- c(S, sort(c, TRUE), 0)
k <- c(0, sort(k), Inf)
kplot <- c()
cplot <- c()

for(i in 1:n){
  kploti <- seq(k[i], k[i+1], length.out = dens)
  kplot <- c(kplot, kploti)
}
kplot <- c(kplot, seq(k[n+1], k[n+1] + 2, length.out = dens))

for(i in 1:(n+1)) cplot <- c(cplot, cfSab(kplot[(dens*(i-1)+1):(dens*i)], seqfSab[i, ]))
  
graf <- ggplot(data.frame(kplot, cplot), aes(x = kplot, y = cplot)) +
  coord_cartesian(xlim = c(0, 16)) +
  labs(x = "Strike", y = "Prêmio", title = "Interpolação de Kahalé") +
  geom_line() +
  geom_point(data = data.frame(x = k[1:(n+1)], y = c[1:(n+1)]), 
             aes(x = x, y = y, color = "salmon")) +
  geom_segment(x = k[1], y = -1, xend = k[1], yend = c[1], color = "salmon") +
  geom_segment(x = k[2], y = -1, xend = k[2], yend = c[2], color = "salmon") +
  geom_segment(x = k[3], y = -1, xend = k[3], yend = c[3], color = "salmon") +
  geom_segment(x = k[4], y = -1, xend = k[4], yend = c[4], color = "salmon") +
  geom_segment(x = k[5], y = -1, xend = k[5], yend = c[5], color = "salmon") +
  
  geom_segment(x = -1, y = c[1], xend = k[1], yend = c[1], color = "salmon") +
  geom_segment(x = -1, y = c[2], xend = k[2], yend = c[2], color = "salmon") +
  geom_segment(x = -1, y = c[3], xend = k[3], yend = c[3], color = "salmon") +
  geom_segment(x = -1, y = c[4], xend = k[4], yend = c[4], color = "salmon") +
  geom_segment(x = -1, y = c[5], xend = k[5], yend = c[5], color = "salmon") +
  geom_segment(x = -1, y = c[6], xend = 20, yend = c[6], color = "salmon") +
  scale_x_continuous(
    breaks = k[1:(n+1)],
    labels = c(expression(k[0] == 0), 
               expression(k[1]), 
               expression(k[2]), 
               expression(k[3]), 
               expression(k[4]))) +
  scale_y_continuous(
    limits = c(0, NA),
    breaks = c,
    labels = c(expression(c[0] == S),
               expression(c[1]),
               expression(c[2]),
               expression(c[3]),
               expression(c[4]),
               expression(c[5] == 0))) +
  theme_bw() +
  theme(legend.position = "none", 
        panel.grid = element_blank(),
        plot.title = element_text(hjust = 0.5))
graf