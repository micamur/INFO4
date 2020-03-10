import math

import matplotlib.pyplot as plt

inpathname = "flt/"

occurences = {}

for i in range(1,3205):
     fileHandler = open (inpathname + "CACM-"+str(i)+".flt", "r")  

     while True:
            line = fileHandler.readline()
            if not line:
                break
            else:
                word = line.strip()
                if word in occurences:
                    occurences[word]+=1
                else:
                    occurences[word]=1
                    
#for key, value in sorted(occurences.items(), key=lambda item: item[1], reverse=True):                 
 #   print(key, "::", value)
 
#print(sorted(occurences.items(), key=lambda item: item[1], reverse=True)[:10])

s = sorted(occurences.items(), key=lambda item: item[1], reverse=True)
sKey10 = [key for (key, value) in s[:10]]
print(sKey10)
sVal10 = [value for (key, value) in s[:10]]
print(sVal10)
print("Taille du vocabulaire", len(s))
#nombre total d'occurence des mots
M = sum([value for (key, value) in s])
print("M", M)
#nombre de mots
My = len(s) 
print("My",My)
l = M/math.log(My)
print("Lambda",l)

x = [i for i in range(1,My+1)]
y = [value for (key, value) in s]
plt.plot(x,y)
plt.title("Courbe expérimentale (en entier)")
plt.xlabel("Rang")
plt.ylabel("Nombre d'occurences")
plt.show()

x = [i for i in range(1,101)]
y = [value for (key, value) in s[:100]]
plt.plot(x,y)

x = [i for i in range(1,100+1)]
y = [l/i for i in range(1,100+1)]
plt.plot(x,y)
plt.title("Courbes théorique et expérimentale (jusqu'à 100)")
plt.xlabel("Rang")
plt.ylabel("Occurences")
plt.show()


