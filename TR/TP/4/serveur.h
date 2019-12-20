#include "shared.h"

// Structure d'un client
typedef struct {
  struct sockaddr *adresse;
  char pseudo[LG_PSEUDO];
  int socket;

  char **messages;
  int nb_messages;
  int size_messages;

  char **abonnements;
  int nb_abonnements;
  int size_abonnements;

  char **abonnes;
  int nb_abonnes;
  int size_abonnes;
} Client;

/* FONCTIONS ******************************************************************/

// Procédure correspondant au traitement du serveur de l'application
void serveur_appli(char *service);

// Permet de passer un nombre de paramètres variable à l'exécutable
void check_arguments(int argc, char *argv[], char *service);

// Initialise les clients
void init_clients();

// Ajoute un client à la liste
void add_client();

// Renvoie l'indice d'un client par rapport à son numéro de socket
int get_client_id_from_socket(int client_socket);

// Renvoie l'indice d'un client par rapport à son pseudo
int get_client_id_from_pseudo(char pseudo[LG_PSEUDO]);

// Renvoie l'indice du pseudo existe déjà dans la liste d'abonnements du client
int find_pseudo_in_subscriptions(Client client, char pseudo[LG_PSEUDO]);

// Renvoie l'indice du pseudo existe déjà dans la liste des abonnés du client
int find_pseudo_in_followers(Client client, char pseudo[LG_PSEUDO]);

// Parse le choix utilisateur et appelle la fonction correspondante
void parse_user_choice(char *choice, Client client);

// Subscribe : s’abonner à un compte en donnant le nom d’un pseudo
void subscribe(Client client, char *pseudo);

// Enlève param dans la liste des abonnements du client
void add_abonnement(Client client, Client param);

// Enlève le client dans la liste des abonnés de param
void add_abonne(Client client, Client param);

// Unsubscribe : se désabonner d'un compte
void unsubscribe(Client client, char *pseudo);

// Enlève param dans la liste des abonnements du client
void remove_abonnement(Client client, Client param);

// Enlève le client dans la liste des abonnés de param
void remove_abonne(Client client, Client param);

// List : lister tous les pseudos auxquels il est abonné
void list(Client client);

// Post : publier un message < 20 caractères à ses abonnés
void post(Client client, char *msg);

// Quit : quitter l’application
void quit(Client client);
