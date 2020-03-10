#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Feb 14 11:23:31 2020

@author: claire
"""
import json
import math
from nltk.tokenize import RegexpTokenizer
from nltk.stem.porter import PorterStemmer

tokenizer = RegexpTokenizer('[A-Za-z]+[A-Za-z0-9]+')

vocpathname = "voc.json"
indinvpathname = "indinv.json"
normdpathname = "normd.json"
inpathAntiDictionary = "cacm/"
inpathname = "fichier_separe/"

#Chargement du vocabulaire
voc = json.load(open(vocpathname,"r"))  

#Chargement de l'index inversé
indinv = json.load(open(indinvpathname,"r"))   

#Chargement de la norme des docucuments 
normd = json.load(open(normdpathname,"r"))  

#nombre de documents dans le corpus
N = 3204

#on recupère l'anti-dico
antidico = []
fileantiD = open (inpathAntiDictionary +"common_words", "r")
while True:
    line = fileantiD.readline()
    if not line :
        break
    else:
        antidico.append(line.strip())

while(True):
    #requete 
    #q = "recipe about samelson perlis"
    q = input("Entrez une requete : ") 
    if q == "quit":
        print("Au revoir")
        break
    elif q== "":
        continue

    #on tokenize les mots de la requete
    tokenq = tokenizer.tokenize(q) 
    print("Token", tokenq)
    
    n = int(input("Entrez le nombres de documents que vous souhaiteriez consulter : ")) 
    
    dicoq = {}
    #on applique l'anti-dico à la requete
    for t in tokenq:
        if t not in antidico:
             #on nettoie les mots
             stemmer = PorterStemmer()
             racine = stemmer.stem(t)
             #si le mot n'ettoyer appartient au voc on l'ajoute
             #et on calcul les tf des mots de la requete
             if racine in voc:
                 if racine in dicoq:
                     dicoq[racine] += 1 
                 else:
                     dicoq[racine] = 1  
                    
    print("tf", dicoq)
    
    if dicoq == {}:
        print("La requete ne correspond à aucun documents")
        continue
        
    #on calcul le poid de chaque terme de la requete         
    for key in dicoq.keys():
        idf = math.log(N/voc[key]) 
        dicoq[key] = dicoq[key] * idf * 1  
            
    print("poid", dicoq)
          
    #on calcul la norme de la requete
    normq = 0
    for w in dicoq:
        normq += dicoq[w]*dicoq[w]
    normq = math.sqrt(normq)  
    print("Norme de la requete", normq)
    
    #calcul intermediaire
    listDoc = {}
    for w in dicoq:
        for i in indinv[w]:
            if i in listDoc:
                listDoc[i] += dicoq[w]*indinv[w][i]
            else:
                listDoc[i] = dicoq[w]*indinv[w][i]
                
    print("calcul intermediaire", listDoc)
    
    #on divise par la norme de la reque * la norme du document
    for d in listDoc:
        listDoc[d] = listDoc[d]/(normq*normd[d])
        
    print("consinus", listDoc)
    
    #on trie
    listSorted = sorted(listDoc.items(), key=lambda t: t[1], reverse=True)
    print(listSorted)
    
    print()
    print("Voici les documents qui correspondent à votre requête")
    #affichage de la première ligne du document pour teaser
    for l in listSorted[:n]:
        print("CACM-"+l[0])
        with open(inpathname+"CACM-"+l[0],"r") as fileHandler:
            head = [next(fileHandler) for x in range(1)]
        print(head[0].strip())
