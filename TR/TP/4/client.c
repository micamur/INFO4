#include "client.h"

// Variables globales car toujours la même valeur et utilisées souvent
// (pour ne pas alourdir les appels de fonction inutilement)
int client_socket = 0;  // numéro de socket du client
char pseudo[LG_PSEUDO]; // pseudo du client

/* DÉMARRAGE DU CLIENT ********************************************************/

int main(int argc, char *argv[]) {
  // serveur est le nom (ou l'adresse IP) auquel le client va acceder
  // service le numero de port sur le serveur pour le client
  char *serveur = SERVEUR_DEFAUT;
  char *service = SERVICE_DEFAUT;

  // Remplissage des deux variables avec les arguments ou les valeurs par défaut
  check_arguments(argc, argv, serveur, service);

  // Création de la socket
  client_socket = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
  if (client_socket == -1) {
    fprintf(stderr, "Erreur création socket\n");
    exit(-1);
  }

  // Initialisation de l'adresse du serveur
  struct sockaddr_in serveur_adresse;
  bzero(&serveur_adresse, sizeof(serveur_adresse));
  serveur_adresse.sin_family = AF_INET;
  serveur_adresse.sin_addr.s_addr = htonl(INADDR_ANY); // accepte tous les msg
  serveur_adresse.sin_port = htons(atoi(service));
  inet_pton(AF_INET, serveur, &serveur_adresse.sin_addr);

  // Connexion au serveur
  if (connect(client_socket, (struct sockaddr *)&serveur_adresse,
              sizeof(struct sockaddr_in)) != 0) {
    fprintf(stderr, "Erreur connexion avec serveur\n");
    exit(-1);
  }
  printf("Succès connection avec serveur (socket %d)\n", client_socket);

  // Démarrage de l'application client
  client_appli(serveur, service);
}

// TODO même si le service en paramètre est différent de celui du serveur,
// le client arrive tout de même à se connecter : est-ce normal ?
void check_arguments(int argc, char *argv[], char *serveur, char *service) {
  switch (argc) {
  // valeurs par defaut
  case 1:
    printf("Serveur par defaut : %s\n", serveur);
    printf("Service par defaut : %s\n", service);
    break;
  // serveur renseigné
  case 2:
    serveur = argv[1];
    printf("Serveur : %s\n", serveur);
    printf("Service par defaut : %s\n", service);
    break;
  // serveur et service renseignés
  case 3:
    serveur = argv[1];
    service = argv[2];
    printf("Serveur : %s\n", serveur);
    printf("Service : %s\n", service);
    break;
  // mauvais nombre d'arguments
  default:
    printf("Usage : ./client serveur(nom ou @IP) service(nom ou port)\n");
    exit(-1);
  }
}

/* TRAITEMENT DU CLIENT *******************************************************/

// TODO read dans chacune des commandes
void client_appli(char *serveur, char *service) {
  // Sélection du pseudo utilisateur
  choose_pseudo(pseudo);
  help();

  // Demande du client envoyée au serveur
  char user_choice;
  do {
    fprintf(stdout, "Entrez une commande (S/U/L/P/Q) : ");
    scanf("%s", &user_choice);
    user_choice = toupper(user_choice);
    parse_user_choice(user_choice);
  } while (user_choice != 'Q');
}

/* INPUT : PSEUDO ET MESSAGE **************************************************/

void choose_pseudo(char pseudo[LG_PSEUDO]) {
  loop_pseudo_length(pseudo);
  if (!check_pseudo_availability(pseudo)) {
    printf("Pseudo indisponible\n");
    exit(-1);
  }
}

void loop_pseudo_length(char pseudo[LG_PSEUDO]) {
  do {
    printf("Entrez un pseudo (%d caractères) : ", LG_PSEUDO);
    scanf("%s", pseudo);
  } while (strlen(pseudo) != LG_PSEUDO);
}

// TODO réponse côté serveur
bool check_pseudo_availability(char pseudo[LG_PSEUDO]) {
  char requete[LG_PSEUDO + 1];
  sprintf(requete, "%s", pseudo);
  write(client_socket, requete, LG_PSEUDO + 1);
  char reponse[1];
  read(client_socket, reponse, LG_RES);
  if (reponse[0] == REPONSE_FALSE[0]) {
    // printf("Pseudo indisponible, veuillez en entrer un nouveau\n");
    return false;
  }
  return true;
}

void loop_message_length(char message[LG_MESSAGE]) {
  do {
    printf("Entrez un message (%d caractères maximum) : ", LG_MESSAGE);
    scanf("%s", message);
  } while (strlen(message) > LG_MESSAGE);
}

/* PAQUETS ********************************************************************/

// Envoie une requête au serveur : caractère de la commande + message
void write_request(char command, char *param) {
  int req_size = 1 + strlen(param);
  char request[req_size];
  sprintf(request, "%c%s", command, param);
  if (write(client_socket, request, req_size) < 0) {
    fprintf(stderr, "Erreur d'écriture\n");
    exit(-1);
  }
}

// Lit et affiche la réponse du serveur pour la liste et les messages reçus
void read_answer() {
  char buffer[REQ_SIZE];
  bzero(buffer, REQ_SIZE);
  int size = read(client_socket, buffer, REQ_SIZE);
  if (size < 0) {
    fprintf(stderr, "Erreur de lecture\n");
    exit(-1);
  }

  // char command = buffer[0];
  printf("%s", buffer);
}

/* CHOIX DE L'UTILISATEUR *****************************************************/

// TODO recevoir messages non lus
void parse_user_choice(char choice) {
  switch (choice) {
  case SUBSCRIBE:
    subscribe();
    break;
  case UNSUBSCRIBE:
    unsubscribe();
    break;
  case LIST:
    list();
    break;
  case POST:
    post();
    break;
  case QUIT:
    quit();
    break;
  case GET:
    get();
    break;
  default:
    help();
    break;
  }
}

void subscribe() {
  printf("À qui souhaitez-vous vous abonner ?\n");
  char param[LG_PSEUDO];
  loop_pseudo_length(param);
  write_request(SUBSCRIBE, param);
  printf("Abonnement : ");
  read_answer();
}

void unsubscribe() {
  printf("De qui souhaitez-vous vous désabonner ?\n");
  char param[LG_PSEUDO];
  loop_pseudo_length(param);
  write_request(UNSUBSCRIBE, param);
  read_answer();
}

// TODO réponse côté serveur + affichage réponse
void list() {
  write_request(LIST, "");
  printf("Abonnements :\n");
  read_answer();
}

// TODO réponse côté serveur + affichage réponse
void post() {
  char message[LG_MESSAGE];
  loop_message_length(message);
  write_request(POST, message);
  read_answer();
}

// TODO réponse côté serveur + affichage réponse
void quit() {
  write_request(QUIT, "");
}

void help() {
  printf("Usage :\n");
  printf("%c = subscribe\n%c = unsubscribe\n%c = list\n%c = post\n%c = quit\n",
         SUBSCRIBE, UNSUBSCRIBE, LIST, POST, QUIT);
}

void get() {
  write_request(GET, "");
  printf("Messages reçus :\n");
  read_answer();
}
