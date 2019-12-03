#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <sys/signal.h>
#include <sys/wait.h>
#include <sys/socket.h>
#include <sys/types.h>

// #include <arpa/inet.h>
// #include <netdb.h>
#include <unistd.h>
#include <netinet/in.h>

// #include "fon.h" /* primitives de la boite a outils */

#define SERVICE_DEFAUT "1111"
#define SERVEUR_DEFAUT "127.0.0.1"

// Définitions de couleurs pour l'affichage
#define RED "\033[38;5;196m"
#define GREEN "\033[38;5;82m"
#define YELLOW "\033[38;5;226m"
#define BLUE "\033[38;5;45m"
#define FUSCHIA "\033[38;5;207m"
#define WHITE "\033[38;5;255m"
#define PURPLE "\033[38;5;105m"
#define ORANGE "\033[38;5;202m"

#define RESET "\033[0m"

#define N 8

// Définition de fonctions pour l'affichage
// Vide l'écran
#define clear() printf("\033[H\033[J")

// Vide la ligne courante
#define clearline() printf("\33[2K\r")

// Déplace le curseur aux coordonés x, y
#define gotoxy(x, y) printf("\033[%d;%dH", (x), (y))

// Déplace le curseur a la ligne précédente
#define gotoprevline(n) printf("\033[%dA", (n))

void client_appli(char *serveur, char *service);

// Parse le choix utilisateur et appelle la fonction correspondante
void user_choice(char c);

// Subscribe : s’abonner à un compte en donnant le nom d’un pseudo
void subscribe();

// Unsubscribe : se désabonner d'un compte
void unsubscribe();

// List : lister tous les pseudos auxquels il est abonné
void list();

// Post : publier un message < 20 caractères à ses abonnés
void post();

// Quit : quitter l’application
void quit();
