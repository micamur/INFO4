#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include <sys/signal.h>
#include <sys/wait.h>
#include <sys/socket.h>

// #include <arpa/inet.h>
// #include <netdb.h>
#include <unistd.h>
#include <netinet/in.h>

#define SERVICE_DEFAUT "1111"
#define NMAX_CLIENTS 10
#define NB_CNX_WAIT 10
#define REQ_SIZE 128

typedef struct {
  char* pseudo;
  char** messages;
  char** abonnements;
  int socket;
  struct sockaddr *adresse;
} Client;

/*initialise le tableau already_found de bool qui permet de savoir quelle pion
 * ont déjà été compté comme au bon endroit ou comme au mauvais endroit*/
void init_bool(int n, bool *already_found);

/*création du paquet à envoyer contenant le nombre de pion au bon endroit et au
 * mauvais endroit*/
void package_to_send(int nb_B, int nb_M, char *msg_send);

/*création du paquet à envoyer quand le joueur à gagné*/
void package_to_send_WIN(int nb_try, char *msg_send);

/*initialise la structure de jeu*/
void *init_game(int n);

/*gere la réponse du joueur et la compare avec la bonne réponse et renvoie les
 * paquets de réponses*/
void process(void *G, char *msg_receive, int socket_client);

/* programme serveur */
void serveur_appli(char *service);

/*vérification arguments*/
void check_arguments(int argc);

int get_client_id_from_socket(Client clients, int client_socket);

/*choix de l'utilisateur*/
void user_choice(char choice, Client client);
