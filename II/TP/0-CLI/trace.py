#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import sys
from math import *

MARGIN = 10
LINEWIDTH = 0.5
RIGHTMAX = 595


def trace(function, xmin, xmax, nstep, output):
    output.write(" x\t %s\n" % function)
    function = eval("lambda x:" + function)
    step = 1. * (xmax - xmin) / nstep
    for i in range(nstep + 1):
        x = xmin + i * step
        try:
            y = function(x)
        except:
            sys.stderr.write(str(x) + "\tERREUR\n")
            continue
        output.write("%s\t%s\n" % (x, y))


def defSavegraphicalstate(output):
    output.write("/cmtx matrix currentmatrix def\n\n")
    output.write("/linestroke {\n")
    output.write("\tgsave\n")
    output.write("\tcmtx setmatrix\n")
    output.write("\tstroke\n")
    output.write("\tgrestore\n")
    output.write("} def\n\n")


def defCm(output):
    output.write("/cm {\n")
    output.write("\t28.3464567 mul\n")
    output.write("} def\n\n")


def defTitle(function, output):
    defCm(output)
    output.write("/titre {\n")
    output.write("\t/Arial findfont\n")
    output.write("\t.5 cm scalefont\n")
    output.write("\tsetfont\n")
    output.write("\t0 0 moveto\n")
    output.write("\t(%s) show\n" % (function))
    output.write("\tlinestroke\n")
    output.write("} def\n\n")


def defAxes(xmin, xmax, ymin, ymax, output):
    output.write("/axes {\n")
    output.write("\t%s 0 moveto\n" % (xmin))
    output.write("\t%s 0 lineto\n" % (xmax))
    output.write("\t0 %s moveto\n" % (ymin))
    output.write("\t0 %s lineto\n" % (ymax))
    output.write("\tlinestroke\n")
    output.write("} def\n\n")


def defGraphe(function, xmin, xmax, nstep, output):
    output.write("/graphe {\n")
    function = eval("lambda x:" + function)
    ymin = inf
    ymax = -inf
    step = 1. * (xmax - xmin) / nstep
    lineto = False
    for i in range(nstep + 1):
        x = xmin + i * step
        try:
            y = function(x)
            ymin = min(ymin, y)
            ymax = max(ymax, y)
            if (lineto):
                output.write("\t%s %s lineto\n" % (x, y))
            else:
                output.write("\t%s %s moveto\n" % (x, y))
            lineto = True
        except:
            lineto = False
    output.write("\tlinestroke\n")
    output.write("} def\n\n")
    return ymin, ymax


def traceg(function, xmin, xmax, nstep, output):
    defSavegraphicalstate(output)
    defTitle(function, output)
    ymin, ymax = defGraphe(function, xmin, xmax, nstep, output)
    defAxes(xmin, xmax, ymin, ymax, output)

    output.write("titre\n")
    output.write("%s %s translate\n" % (MARGIN, MARGIN))
    output.write("%s %s scale\n" % ((RIGHTMAX - 2 * MARGIN) /
                                    (xmax - xmin), (RIGHTMAX - 2 * MARGIN) / (xmax - xmin)))
    output.write("%s %s translate\n" % (-xmin, -ymin))
    output.write("graphe\n")
    output.write("axes\n")


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

    print("\nL'argument FONCTION est une fonction mathématique (ou\nplusieurs en non graphique) de la librairie math de Python.")
    print("Toutes les fonctions disponibles : https://docs.python.org/3/library/math.html")

    print("\nExemples :")
    print("\t./trace.py \"cos(x)\"\t\tAffiche 10 points entre 0 et 1 de la fonction cos")
    print("\t./trace.py -o fichier \"cos(x)\"\tÉcrit dans fichier le même résultat\n\t\t\t\t\tque la commande précédente")
    print("\t./trace.py \"cos(x)\" --graphic\tAffiche le script PS de la même fonction\n\t\t\t\t\tque la commande précédente")
    print("\t./trace.py -xmin -1 \"cos(x)\"\tAffiche 10 points entre -1 et 1 de la fonction cos")
    print("\t./trace.py \"cos(x)\" \"sin(x)\"\tAffiche 10 points entre 0 et 1 des fonctions cos et sin")
    print("\t\t\t\t\t(plusieurs fonctions seulement en non graphique)")


def main(argv=None):
    if argv is None:
        argv = sys.argv

    import getopt

    try:
        options, argv = getopt.getopt(
            argv[1:], "o:hg", ["output=", "help", "xmin=", "xmax=", "nstep=", "graphic"])
    except getopt.GetoptError as message:
        sys.stderr.write("%s\n" % message)
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
            nstep = int(value)
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
        sys.exit(1)

    for function in argv:
        if (graphic):
            traceg(function, xmin, xmax, nstep, output)
        else:
            trace(function, xmin, xmax, nstep, output)


if __name__ == "__main__":
    sys.exit(main())
