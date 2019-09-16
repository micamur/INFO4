#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import sys
from math import *


def trace(function, xmin, xmax, nstep, output):
    output.write(" x\t %s\n" % function)
    function = eval("lambda x:" + function)

    step = 1.*(xmax-xmin)/nstep
    for i in range(nstep+1):
        x = xmin + i*step
        try:
            y = function(x)
        except:
            sys.stderr.write(str(x) + "\tERREUR\n")
            continue
        output.write("%s\t%s\n" % (x, y))


# TODO utiliser brouillon pour conversions
def traceg(function, xmin, xmax, nstep, output):
    function = eval("lambda x:" + function)

    ymin = inf
    ymax = -inf

    step = 1.*(xmax-xmin)/nstep
    for i in range(nstep+1):
        x = xmin + i*step
        try:
            y = function(x)
            ymin = min(ymin, y)
            ymax = max(ymax, y)
        except:
            # sys.stderr.write(str(x) + "\tERREUR\n") # TODO réfléchir
            continue
        # output.write("%s\t%s\n" % (x, y)) # TODO dans fichier PostScript


def usage():
    print("Utilisation : ./trace.py [OPTION]... [FONCTION]...")
    
    print("\nCalcule et affiche des points d'une FONCTION passée en paramètre.")
    print("Par défaut, xmin = 0, xmax = 1 et nstep = 10.")

    print("\nOptions :")
    print("\t-o,\t--output=FICHIER\tfichier de sortie")
    print("\t-h,\t--help\t\t\tafficher l'aide et quitter")
    print("\t\t--xmin=XMIN\t\tborne minimum")
    print("\t\t--xmax=XMAX\t\tborne maximum")
    print("\t\t--nstep=NSTEP\t\tnombre de pas")
    print("\t-g,\t--graphic\t\tversion graphique")

    print("\nL'argument FONCTION est une (ou plusieurs) fonction(s)\nmathématique(s) de la librairie math de Python.")
    print("Toutes les fonctions disponibles : https://docs.python.org/3/library/math.html")

    print("\nExemples :")
    print("\t./trace.py \"cos(x)\"\t\tAffiche 10 points entre 0 et 1 de la fonction cos")
    print("\t./trace.py -o fichier \"cos(x)\"\tÉcrit dans fichier le même résultat\n\t\t\t\t\tque la commande précédente")
    print("\t./trace.py -xmin -1 \"cos(x)\"\tAffiche 10 points entre -1 et 1 de la fonction cos")
    print("\t./trace.py \"cos(x)\" \"sin(x)\"\tAffiche 10 points entre 0 et 1 des fonctions cos et sin")

def main(argv=None):
    if argv is None:
        argv = sys.argv

    import getopt

    try:
        options, argv = getopt.getopt(argv[1:], "o:hg", ["output=", "help", "xmin=", "xmax=", "nstep=", "graphic"])
    except getopt.GetoptError as message:
        sys.stderr.write("%s\n" % message)  # TODO lister les options
        sys.exit(1)

    output = sys.stdout
    xmin, xmax = 0., 1.
    nstep = 10
    graphic = False

    for option, value in options:
        if option in ["-o", "--output"]:
            output = open(value, "w")
        elif option == "--xmin":
            xmin = float(value)
        elif option == "--xmax":
            xmax = float(value)
        elif option == "--nstep":
            nstep = float(value)
        elif option in ["-g", "--graphic"]:
            graphic = True
        elif option in ["-h", "--help"]:
            usage()
            sys.exit()
        else:
            assert False, "unhandled option"

    if len(argv) == 0:
        sys.stderr.write(
            "Quelle fonction voulez-vous ? Exemple : ./trace.py \"sin(x)\"\n")
        # TODO si >1 args : afficher la première fonction + s'excuser à l'utilisateur
        sys.exit(1)

    for function in argv:
        if (graphic):
            traceg(function, xmin, xmax, nstep, output)
        else:
            trace(function, xmin, xmax, nstep, output)


if __name__ == "__main__":
    sys.exit(main())
