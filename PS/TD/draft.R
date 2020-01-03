generateur3 = function(N) {
  ifelse(runif(N, 0, 1)**2 + runif(N, 0, 1)**2 < 1, 4, 0)
}

N = 10000
X = generateur(N)
mexp = mean(X)
mth = pi
vexp = var(X)
vth = 4*pi - pi**2

###############################################################################

n = 10000
k = 100

generateur = function(n, k) {
  ones = rep(1, k)
  zeroes = rep(0, n-k)
  bits = sample(x=c(ones, zeroes), n, replace=FALSE)
  index = which(bits %in% 1)
  x = sum(2**index)
  return(bits)
}

generateur(n, k)

# n appels à random donc coût de n

###### WIP

#probas = rep(0, n)
#for (i in 1:k) {
#  probas[i] = comb(n, i)
#}
#tot = sum(probas)
#probas = probas / tot

#kinf = sample(1, 0, k)

#generateur(n, kinf)

###############################################################################

