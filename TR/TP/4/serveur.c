#include "serveur.h"

int main(int argc, char *argv[]) {
  char *service = SERVICE_DEFAUT; /* numero de service par defaut */

  check_arguments(argc);

  /* Permet de passer un nombre de parametre variable a l'executable */
  switch (argc) {
  case 1: /*si il n'y a pas d'argument on prend le service par defaut*/
    printf("defaut service = %s\n", service);
    break;
  case 2: /*sinon on prend celui passé en paramêtre*/
    service = argv[1];
    break;

  default:
    printf("Usage:serveur service (nom ou port) \n");
    exit(1);
  }

  /* service est le service (ou numero de port) auquel sera affecte
  ce serveur*/
  srand(time(NULL)); /*permet d'initialiser srand pour la fonction init_game*/
  serveur_appli(service);
}

/******************************************************************************/

/* Procedure correspondant au traitemnt du serveur de votre application */
void serveur_appli(char *service) {
  struct sockaddr_in serveur_adresse; // adresse IP du serveur
  int serveur_socket;                 // port du serveur
  Client clients[NMAX_CLIENTS];       // tableau contenant tous les clients
  char msg_received[REQ_SIZE]; // buffer qui contiendra les messages reçus
  fd_set set, setbis;
  int socket_max;
  // char buff[1000];
  // int nb_known_sockets=0;

  // Initialisation sockets clients
  FD_ZERO(&set);

  // Création socket serveur
  serveur_socket = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
  if (serveur_socket == -1) {
    fprintf(stderr, "Échec création socket serveur.\n");
    exit(-1);
  } else {
    printf("Succès création socket serveur : %d.\n", serveur_socket);
  }

  socket_max = serveur_socket;  // TODO
  FD_SET(serveur_socket, &set); // ajout du socket du serveur à l’ensemble set
  bzero(&serveur_adresse, sizeof(serveur_adresse)); // TODO

  serveur_adresse.sin_family = AF_INET;
  serveur_adresse.sin_addr.s_addr = htonl(INADDR_ANY); // accepte tous les msg
  serveur_adresse.sin_port = htons(atoi(service));

  // adr_socket(service, "127.0.0.1", SOCK_STREAM, &padr_local);
  // parametre padr_local

  // Définit un point d'accès local pour la socket de numéro serveur_socket
  if (bind(serveur_socket, (struct sockaddr *)&serveur_adresse,
           sizeof(serveur_adresse)) != 0) {
    fprintf(stderr, "Échec bind\n");
    exit(-1);
  } else {
    printf("Succès bind\n");
  }

  // On place le processus en attente de demande de connexion du client.
  if (listen(serveur_socket, NB_CNX_WAIT) != 0) {
    fprintf(stderr, "Échec listen\n");
    exit(-1);
  } else {
    printf("Succès listen\n");
  }

  // On arrive à cet endroit du programme lorsque le serveur à reçu une demande
  // On accepte la demande sur la socket initialement créée
  socklen_t longueur = sizeof(clients[0]);

  // TODO remplir le tableau

  while (true) {
    int client_socket = accept(serveur_socket, 0, &longueur);
    if (client_socket != 0) {
      fprintf(stderr, "Échec accept\n");
      exit(-1);
    } else {
      fprintf(stderr, "Succès accept client %d\n", client_socket);
      FD_SET(client_socket, &set);
      // inserer(client_socket, &nb_known_sokets, known_sockets);
    }

    bcopy((char *)&set, (char *)&setbis, sizeof(set));

    int client_id = get_client_id_from_socket(clients, client_socket);

    for (int i = 0; i < NMAX_CLIENTS; i++) {
      if (FD_ISSET(clients[client_id].socket, &set)) {
        bzero(msg_received, REQ_SIZE);
      }
      read(clients[client_id].socket, msg_received, REQ_SIZE);
    }

    /* a voir comment utiliser
      bcopy((char *)&set, (char *)&setbis, sizeof(set));
      /* copie de l’ensemble set dans setbis */
    // for (...;...;...) {
    //   select(socket_max, &set, 0, 0, 0);
    //   if (FD_ISSET(idsock1, &set)) /* Test si idsock1 appartient à set */
    //     continue;
    //   if (FD_ISSET(idsock2, &set))
    //     bcopy((char *)&setbis, (char *)&set, sizeof(set));
    // }

    // on lis le message reçu et on le met dans msg_received
    read(clients[client_id].socket, msg_received, REQ_SIZE);
    // on regarde qu'elle est la première lettre du message
    user_choice((char)msg_received[0], clients[client_id]);


    //
    bcopy((char *)&setbis, (char *)&set, sizeof(set));
  }

  // Fermeture connexion
  close(serveur_socket);
}

void check_arguments(int argc) {
  if (argc != 2) {
    fprintf(stderr, "Argument : numéro de port\n");
    exit(-1);
  }
}

int get_client_id_from_socket(Client clients, int client_socket) {
  for (int i = 0; i < NMAX_CLIENTS; i++) {
    return 0; // TODO recherche socket dans les clients
  }
}

// TODO création socket serveur
void init_serveur_socket() {}

void user_choice(char choice, Client client) {
  switch (choice) {
  // Subscribe : s'abonner à un compte en donnant le nom d'un pseudo
  case 'S':
    printf("Coucou\n");
    break;
  // Unsubscribe : se désabonner d'un compte
  case 'U':
    printf("Coucou\n");
    break;
  // List : lister tous les pseudos auxquels il est abonné
  case 'L':
    printf("Coucou\n");
    break;
  // Post : publier un message < 20 caractères à ses abonnés
  case 'P':
    printf("Coucou\n");
    break;
  // Quit : quitter l'application
  case 'Q':
    printf("Coucou\n");
    // c_quit();
    close(client.socket);
    break;
  default:
    break;
  }
}
