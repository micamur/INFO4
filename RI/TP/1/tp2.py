#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jan 31 10:46:41 2020

@author: claire
"""
from nltk.stem.porter import PorterStemmer
import json
import math

outpathname = "sttr/"
inpathname = "flt/"
inpathAntiDictionary = "cacm/"
vocpathname = "voc.json"
indinvpathname = "indinv.json"
normdpathname = "normd.json"
antidico = []
fileantiD = open (inpathAntiDictionary +"common_words", "r")
while True:
    line = fileantiD.readline()
    if not line :
        break
    else:
        antidico.append(line.strip())
          
voc = {}   
N=3204    
tf = [{}]*(N+1)
df = {}
d = [{}]*(N+1)

for i in range(1,N+1):
     fileHandler = open (inpathname + "CACM-"+str(i)+".flt", "r")
     
     f = open(outpathname+"CACM-"+str(i)+".sttr","w+")
     d[i] = {}
     tf[i] = {}
      
     while True:
            line = fileHandler.readline()
            if not line :
                #on remplis document frequency
                for w in tf[i]:
                    if w in df:
                        df[w]+=1
                    else:
                        df[w]=1
                break
            else:
                word = line.strip()
                #on ecrit seulement les mots qui ne
                #sont pas dans l'antidictionaire
                if word not in antidico:
                    #on nettoie les mots
                    stemmer = PorterStemmer()
                    racine = stemmer.stem(word)
                    #on remplis le vocabulaire
                    if racine in voc:
                        voc[racine] += 1
                    else:
                        voc[racine] = 1
                     #on remplis term frequency
                    if racine in tf[i]:
                         tf[i][racine]+=1
                    else:
                        tf[i][racine]=1 
                    #on ecrit le document simplifié
                    f.write(racine+"\n")
                    
#on sauvegarde le vocabulaire dans un json
json.dump(voc,open(vocpathname,"w"))     

#on remplis le vecteur de Salton
for i in range(1,N+1):
    for w in tf[i]:
        idf = math.log(N/df[w])
        d[i][w]= tf[i][w] * idf * 1

print("document frequency :", df["termin"])

#on remplis l'index inversé
indinv = {} 
for terme in df:
    indinv[terme] = {}
    for i in range(1,N+1):
        if terme in tf[i]:
            indinv[terme][i] = d[i][terme]
            
#on sauvegarde l'index inversé dans un json
json.dump(indinv,open(indinvpathname,"w"))   

normd = {}
for i in range(1,N+1):
    normd[i]=0
    for w in d[i]:
        normd[i] += d[i][w]*d[i][w]
    normd[i] = math.sqrt(normd[i])

#on sauvegarde la norme des documents dans un json
json.dump(normd,open(normdpathname,"w"))  
    