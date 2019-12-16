#include "shared.h"

/* DÉFINITIONS ****************************************************************/

// Couleurs
#define RED "\033[38;5;196m"
#define GREEN "\033[38;5;82m"
#define YELLOW "\033[38;5;226m"
#define BLUE "\033[38;5;45m"
#define FUSCHIA "\033[38;5;207m"
#define WHITE "\033[38;5;255m"
#define PURPLE "\033[38;5;105m"
#define ORANGE "\033[38;5;202m"
#define RESET "\033[0m"

// Vide l'écran
#define clear() printf("\033[H\033[J")

// Vide la ligne courante
#define clearline() printf("\33[2K\r")

// Déplace le curseur aux coordonés x, y
#define gotoxy(x, y) printf("\033[%d;%dH", (x), (y))

// Déplace le curseur a la ligne précédente
#define gotoprevline(n) printf("\033[%dA", (n))

/* FONCTIONS ******************************************************************/

// Procédure correspondant au traitement d'un client de l'application
void client_appli(char *serveur, char *service);

// Permet de passer un nombre de paramètres variable à l'exécutable
void check_arguments(int argc, char *argv[], char *serveur, char *service);

// Parse le choix utilisateur et appelle la fonction correspondante
void parse_user_choice(char c);

// Définit le pseudo choisi par l'utilisateur
void choose_pseudo(char pseudo[LG_PSEUDO]);

// Boucle tant que le pseudo choisi n'est pas de la bonne longueur
void loop_pseudo_length(char pseudo[LG_PSEUDO]);

// Renvoie true si le pseudo est disponible
bool check_pseudo_availability(char pseudo[LG_PSEUDO]);

// Boucle tant que le message choisi n'est pas de la bonne longueur
void loop_message_length(char message[LG_MESSAGE]);

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

// Help : aide de l’application, liste des commandes
void help();
