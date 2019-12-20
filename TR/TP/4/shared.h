#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <sys/signal.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/wait.h>

// #include <netdb.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <unistd.h>

// Valeur par défaut
#define SERVEUR_DEFAUT "127.0.0.1"
#define SERVICE_DEFAUT "10000"
#define NB_MESSAGES_DEFAULT 8
#define NB_ABONNEMENTS_DEFAULT 8
#define NB_ABONNES_DEFAULT 8

#define NMAX_CLIENTS 8
#define NB_CNX_WAIT NMAX_CLIENTS

// Paramètres
#define LG_PSEUDO 6
#define LG_MESSAGE 20
#define LG_RES 1
#define REPONSE_TRUE '1'
#define REPONSE_FALSE '0'
#define REQ_SIZE 128

// Commandes
#define SUBSCRIBE 'S'
#define UNSUBSCRIBE 'U'
#define LIST 'L'
#define POST 'P'
#define QUIT 'Q'
#define GET 'G'
