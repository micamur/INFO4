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
  printf("Succès connection avec serveur (client %d)\n", client_socket);

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
    parse_user_choice(user_choice);
  } while (user_choice != 'Q');
}

/* INPUT : PSEUDO ET MESSAGE **************************************************/

void choose_pseudo(char pseudo[LG_PSEUDO]) {
  bool pseudo_available = false;
  while (!pseudo_available) {
    loop_pseudo_length(pseudo);
    pseudo_available = check_pseudo_availability(pseudo);
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
  // char requete[1 + LG_PSEUDO];
  // sprintf(requete, "C%s", pseudo);
  // write(client_socket, requete, 1 + LG_PSEUDO);
  // char reponse[1];
  // read(client_socket, reponse, LG_RES);
  // if (reponse[0] == REPONSE_FALSE) {
  //   printf("Pseudo indisponible, veuillez en entrer un nouveau\n");
  //   return false;
  // }
  return true;
}

void loop_message_length(char message[LG_MESSAGE]) {
  do {
    printf("Entrez un message (%d caractères maximum) : ", LG_MESSAGE);
    scanf("%s", message);
  } while (strlen(message) > LG_MESSAGE);
}

/* CHOIX DE L'UTILISATEUR *****************************************************/

// TODO recevoir messages non lus
void parse_user_choice(char choice) {
  switch (toupper(choice)) {
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
  // case 'R':
  //   unread_messages();
  //   break;
  default:
    help();
    break;
  }
}

// TODO réponse côté serveur + affichage réponse
void subscribe() {
  printf("%c = subscribe\n", SUBSCRIBE);

  printf("À qui souhaitez-vous vous abonner ?\n");
  char param[LG_PSEUDO];
  choose_pseudo(param);

  char requete[1 + LG_PSEUDO];
  sprintf(requete, "S%s", param);

  write(client_socket, requete, 1 + LG_PSEUDO);

  // Affichage de la réponse du serveur
  char reponse[strlen("subscribe ok") + 1];
  read(client_socket, reponse, strlen("subscribe ok"));
  printf("%s\n", reponse);
}

// TODO réponse côté serveur + affichage réponse
void unsubscribe() {
  printf("%c = unsubscribe\n", UNSUBSCRIBE);

  printf("De qui souhaitez-vous vous désabonner ?\n");
  char param[LG_PSEUDO];
  choose_pseudo(param);

  char requete[1 + LG_PSEUDO];
  sprintf(requete, "U%s", param);

  write(client_socket, requete, 1 + LG_PSEUDO);

  // Affichage de la réponse du serveur
  char reponse[strlen("unsubscribe ok") + 1];
  read(client_socket, reponse, strlen("unsubscribe ok"));
  printf("%s\n", reponse);
}

// TODO réponse côté serveur + affichage réponse
void list() {
  printf("%c = list\n", LIST);

  write(client_socket, "L", 1);

  // TODO Boucle while qui lit des pseudos de 6 caractères jusqu'à lire NULL
  char reponse[strlen("list ok") + 1];
  read(client_socket, reponse, strlen("list ok"));
  printf("%s\n", reponse);
}

// TODO réponse côté serveur + affichage réponse
void post() {
  printf("%c = post\n", POST);

  char message[LG_MESSAGE];
  loop_message_length(message);

  char requete[1 + LG_MESSAGE];
  sprintf(requete, "P%s", message);

  write(client_socket, requete, 1 + LG_MESSAGE);

  // Affichage de la réponse du serveur
  char reponse[strlen("post ok") + 1];
  read(client_socket, reponse, strlen("post ok"));
  printf("%s\n", reponse);
}

// TODO réponse côté serveur + affichage réponse
void quit() {
  printf("%c = quit\n", QUIT);

  write(client_socket, "Q", 1);

  // Affichage de la réponse du serveur
  char reponse[strlen("quit ok") + 1];
  read(client_socket, reponse, strlen("quit ok"));
  printf("%s\n", reponse);

  close(client_socket);
}

void help() {
  printf("Usage :\n");
  printf("%c = subscribe\n%c = unsubscribe\n%c = list\n%c = post\n%c = quit\n",
         SUBSCRIBE, UNSUBSCRIBE, LIST, POST, QUIT);
}
