# MAKEFILE MASTERMIND ##########################################################

# OBJ1 = fon.o client.o
# OBJ2 = fon.o serveur.o

# ADAPTATION AUX DIFFÉRENTS SYSTÈMES D'EXPLOITATION ############################

OPTIONS	=
# Adaptation a Darwin / MacOS X avec fink
# Du fait de l'absence de libtermcap on se fait pas mal
# cracher dessus mais ca marche...
ifeq ($(shell uname), Darwin)
LFLAGS	+= -L/opt/local/lib
CFLAGS	+= -I /opt/local/include
endif
#Changer si necessaire le chemin d'acces aux librairies

# Adaptation a Linux
ifeq ($(shell uname), Linux)
OPTIONS	+= -ltermcap
endif

# Adaptation a FreeBSD
# Attention : il faut utiliser gmake...
ifeq ($(shell uname),FreeBSD)
OPTIONS	+= -ltermcap
endif

# Adaptation a Solaris
ifeq ($(shell uname),SunOS)
OPTIONS	+= -ltermcap  -lsocket -lnsl
CFLAGS	+= -I..
endif

################################################################################

# EXEC = ${OBJ1} client ${OBJ2} serveur
# all: ${EXEC}
#
# # fon.o :  fon.h fon.c
# # 	gcc -DDEBUG -c fon.c
#
# client.o : client.c # fon.h
# 	gcc  $(CFLAGS) -c  client.c
#
# serveur.o : serveur.c # fon.h
# 	gcc  $(CFLAGS) -c  serveur.c
#
# client : ${OBJ1}
# 	gcc $(LFLAGS) ${OBJ1} -o client // $(OPTIONS)
#
# serveur : ${OBJ2}
# 	gcc $(LFLAGS) ${OBJ2} -o serveur // $(OPTIONS)
#
# clean :
# 	rm -f ${EXEC} core

# MAKEFILE SUJET ###############################################################

#commentaires
#définitions des fichiers objets comme une définition d’une constante en C
#(copie /collé dans la suite du fichier)
OBJ1 = client.o
OBJ2 = serveur.o
EXEC = ${OBJ1} client ${OBJ2} serveur
#But du makefile : créer ces fichiers
all: ${EXEC}
#Pour chacun d’eux on donne : son nom suivi des fichiers dont il dépend
#puis la commande de compilation qui le créera
# fon.o : fon.h fon.c
# 	gcc -c fon.c
client.o : client.c client.h
	gcc -c client.c
serveur.o : serveur.c serveur.h
	gcc -c serveur.c
client : ${OBJ1}
	gcc ${OBJ1} -o client -lcurses  -lnsl -ltermcap # $(OPTIONS)
serveur : ${OBJ2}
	gcc ${OBJ2} -o serveur -lcurses  -lnsl -ltermcap # $(OPTIONS)
#permet de détruire tous les fichiers voulu (fichiers créés et core éventuel)
#par la commande make cl
