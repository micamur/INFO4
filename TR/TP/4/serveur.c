#include "serveur.h"

/*
Valeur globale contenant le numéro de socket.
Elle est globale car on l'utilise souvent et que ce sera la même pendant toute
l'exécution du programme. La passer en paramètre alourdirait les appels de
fonction inutilement.
*/
int serveur_socket = 0;
Client *clients; // tableau de tous les clients (de taille NMAX_CLIENTS)

/* DÉMARRAGE DU SERVEUR *******************************************************/

int main(int argc, char *argv[]) {
  // service le numero de port du serveur
  char *service = SERVICE_DEFAUT; /* numero de service par defaut */

  // Remplissage du service avec les arguments ou les valeurs par défaut
  check_arguments(argc, argv, service);

  // Création socket serveur
  serveur_socket = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
  if (serveur_socket == -1) {
    fprintf(stderr, "Échec création socket serveur\n");
    exit(-1);
  } else {
    printf("Succès création serveur (socket %d)\n", serveur_socket);
  }

  // Démarrage de l'application serveur
  serveur_appli(service);
}

void check_arguments(int argc, char *argv[], char *service) {
  switch (argc) {
  // valeur par defaut
  case 1:
    printf("Service par defaut : %s\n", service);
    break;
  // service renseigné
  case 2:
    service = argv[1];
    printf("Service : %s\n", service);
    break;
  // mauvais nombre d'arguments
  default:
    printf("Usage : ./serveur service(nom ou port)\n");
    exit(1);
  }
}

/* TRAITEMENT DU SERVEUR ******************************************************/

// TODO refonte totale du serveur
// TODO plusieurs clients
void serveur_appli(char *service) {
  struct sockaddr_in serveur_adresse; // adresse IP du serveur
  fd_set set;                         // liste des sockets prêts à lire
  int socket_max;                     // numéro maximum de socket
  char buffer[REQ_SIZE];              // buffer des messages reçus

  // Initialisation du nombre maximum de sockets
  socket_max = getdtablesize();

  // Initialisation de l'adresse du serveur
  bzero(&serveur_adresse, sizeof(serveur_adresse));
  serveur_adresse.sin_family = AF_INET;
  serveur_adresse.sin_addr.s_addr = htonl(INADDR_ANY); // accepte tous les msg
  serveur_adresse.sin_port = htons(atoi(service));

  // Définit un point d'accès local pour la socket du serveur
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
  init_clients();

  while (true) {
    // Initialisation de l'ensemble des sockets à écouter
    FD_ZERO(&set);
    FD_SET(serveur_socket, &set); // serveur
    for (int i = 0; i < NMAX_CLIENTS; i++) {
      if (clients[i].socket != -1) {
        FD_SET(clients[i].socket, &set); // client
      }
    }

    // Sélection
    if (select(socket_max, &set, 0, 0, 0) <= 0) {
      fprintf(stderr, "Échec select\n");
      exit(0);
    }

    // Si le serveur est prêt c'est qu'un nouveau client veut communiquer
    if (FD_ISSET(serveur_socket, &set)) {
      add_client(set);
    }

    // Si un client veut communiquer il veut effectuer une action
    for (int i = 0; i < NMAX_CLIENTS; i++) {
      if (FD_ISSET(clients[i].socket, &set)) {
        // on lit le message reçu et on le met dans buffer
        memset(buffer, 0, sizeof(buffer));
        read(clients[i].socket, buffer, REQ_SIZE);
        // on choisit une action en fonction du message
        parse_user_choice(buffer, i);
      }
    }
  }
}

void init_clients() {
  clients = malloc(sizeof(Client) * NMAX_CLIENTS);
  for (int i = 0; i < NMAX_CLIENTS; i++) {
    clients[i].adresse = NULL;
    sprintf(clients[i].pseudo, "user_%d", i);
    clients[i].socket = -1;

    clients[i].nb_messages = 0;
    clients[i].size_messages = NB_MESSAGES_DEFAULT;
    clients[i].messages = malloc(clients[i].size_messages * sizeof(char *));

    clients[i].nb_abonnements = 0;
    clients[i].size_abonnements = NB_ABONNEMENTS_DEFAULT;
    clients[i].abonnements =
        malloc(clients[i].size_abonnements * sizeof(char *));

    clients[i].nb_abonnes = 0;
    clients[i].size_abonnes = NB_ABONNES_DEFAULT;
    clients[i].abonnes = malloc(clients[i].size_abonnes * sizeof(char *));
  }
}

// TODO récupérer pseudo et vérifier s'il existe dans la base d'utilisateurs
// TODO réponse au client
void add_client() {
  socklen_t longueur = sizeof(struct sockaddr *);
  struct sockaddr *client_adresse = NULL;

  // Si la connexion à la socket n'a pas fonctionné
  int client_socket = accept(serveur_socket, client_adresse, &longueur);
  if (client_socket < 0) {
    fprintf(stderr, "Échec accept\n");
    exit(-1);
  }

  // Si le pseudo n'existe pas
  char login[LG_PSEUDO + 1];
  read(client_socket, login, LG_PSEUDO + 1);
  // printf("%s\n",login );
  int client_id = get_client_id_from_pseudo(login);
  if (client_id == -1) {
    fprintf(stderr, "%s n'existe pas dans la base d'utilisateurs\n", "TODO");
    write(client_socket, REPONSE_FALSE, 1);
  } else {
    write(client_socket, REPONSE_TRUE, 1);

    // Initialisation de la socket dans la liste des clients
    clients[client_id].socket = client_socket;
    clients[client_id].adresse = client_adresse;

    fprintf(stderr, "Succès accept client (socket %d)\n", client_socket);
  }
}

/* RECHERCHE D'IDENTIFIANT ****************************************************/

int get_client_id_from_socket(int client_socket) {
  for (int i = 0; i < NMAX_CLIENTS; i++)
    if (clients[i].socket == client_socket)
      return i;
  return -1;
}

int get_client_id_from_pseudo(char pseudo[LG_PSEUDO]) {
  for (int i = 0; i < NMAX_CLIENTS; i++)
    if (strcmp(clients[i].pseudo, pseudo) == 0)
      return i;
  return -1;
}

int find_pseudo_in_subscriptions(Client client, char pseudo[LG_PSEUDO]) {
  for (int i = 0; i < client.nb_abonnements; i++)
    if (strcmp(client.abonnements[i], pseudo) == 0)
      return i;
  return -1;
}

int find_pseudo_in_followers(Client client, char pseudo[LG_PSEUDO]) {
  for (int i = 0; i < client.nb_abonnements; i++)
    if (strcmp(client.abonnes[i], pseudo) == 0)
      return i;
  return -1;
}

/* PAQUETS ********************************************************************/

// Envoie une requête au serveur : caractère de la commande + message
void write_answer(Client client, char *param) {
  int req_size = 1 + strlen(param);
  char request[req_size];
  sprintf(request, "%s\n", param);
  if (write(client.socket, request, req_size) < 0) {
    fprintf(stderr, "Erreur d'écriture\n");
    exit(-1);
  }
}

/* CHOIX DE L'UTILISATEUR *****************************************************/

// TODO envoyer messages non lus
void parse_user_choice(char *choice, int id_client) {
  printf("User, choice : %s, %s\n", clients[id_client].pseudo, choice);
  switch (choice[0]) {
  case 'S':
    subscribe(id_client, choice + 1);
    break;
  case 'U':
    unsubscribe(id_client, choice + 1);
    break;
  case 'L':
    list(id_client);
    break;
  case 'P':
    post(id_client, choice + 1);
    break;
  case 'Q':
    quit(id_client);
    break;
  // case 'R':
  //   unread_messages();
  //   break;
  default:
    printf("Commande inconnue\n");
    break;
  }
}

// TODO réponse au client
// TODO erreur quand le client fournit le pseudo
void subscribe(int id_client, char *pseudo) {
  int id_abonnement = get_client_id_from_pseudo(pseudo);
  Client client = clients[id_client];

  // Le pseudo donné en argument n'existe pas dans la liste des clients
  if (id_abonnement == -1) {
    printf("%s n'existe pas\n", pseudo);
    write_answer(client, "pseudo inexistant");
  }

  // Le pseudo donné en paramètre est celui du client
  else if (strcmp(client.pseudo, pseudo) == 0) {
    printf("%s ne peut s'abonner à lui-même\n", client.pseudo);
    write_answer(client, "abonnement à soi-même impossible");
  }

  // Le pseudo donné en paramètre existe déjà dans les abonnements du client
  else if (find_pseudo_in_subscriptions(client, pseudo) != -1) {
    printf("%s est déjà dans les abonnements de %s\n", pseudo, client.pseudo);
    write_answer(client, "déjà abonné");
  }

  // On ajoute un pseudo à la liste des abonnements du client
  else {
    add_abonnement(id_client, id_abonnement);
    printf("%s abonné à %s\n", client.pseudo, pseudo);
    write_answer(client, "succès");
  }
}

// Client est abonné à param
void add_abonnement(int id_client, int id_param) {
  // Si la liste d'abonnements est pleine on double sa taille
  if (clients[id_client].nb_abonnements ==
      clients[id_client].size_abonnements) {
    clients[id_client].size_abonnements *= 2;
    clients[id_client].abonnements =
        (char **)realloc(clients[id_client].abonnements,
                         sizeof(char *) * clients[id_client].size_abonnements);
  }

  // On ajoute un pseudo à la liste des abonnements du client
  clients[id_client].abonnements[clients[id_client].nb_abonnements++] =
      clients[id_param].pseudo;

  add_abonne(id_client, id_param);
}

// Param a comme abonné client
void add_abonne(int id_client, int id_param) {
  // Si la liste des abonnes est pleine on double sa taille
  if (clients[id_param].nb_abonnes == clients[id_param].size_abonnes) {
    clients[id_param].size_abonnes *= 2;
    clients[id_param].abonnes =
        (char **)realloc(clients[id_param].abonnes,
                         sizeof(char *) * clients[id_param].size_abonnes);
  }

  // On ajoute le client à la liste des abonnés du param
  clients[id_param].abonnes[clients[id_param].nb_abonnes++] =
      clients[id_client].pseudo;
}

// TODO réponse au client
// TODO erreur quand le client fournit le pseudo
void unsubscribe(int id_client, char *pseudo) {
  // int id_pseudo_global = get_client_id_from_pseudo(pseudo);
  //
  // // Le pseudo donné en argument n'existe pas dans la liste des clients
  // if (id_pseudo_global == -1) {
  //   printf("%s n'existe pas\n", pseudo);
  //   return;
  // }
  //
  // Client param = clients[id_pseudo_global];
  //
  // // On enlève l'abonnement à pseudo dans client
  // remove_abonnement(client, param);
  //
  // // On enlève l'abonnement de client dans pseudo
  // remove_abonne(client, param);
}

void remove_abonnement(Client client, Client param) {
  int id_pseudo_in_abonnements =
      find_pseudo_in_subscriptions(client, param.pseudo);

  // Le pseudo donné en paramètre n'existe pas dans les abonnements du client
  if (id_pseudo_in_abonnements == -1) {
    printf("%s n'est pas dans les abonnements de %s\n", param.pseudo,
           client.pseudo);
    return;
  }

  // On enleve le pseudo de la liste des abonnements
  for (int i = id_pseudo_in_abonnements; i < client.nb_abonnements; i++) {
    client.abonnements[i] = client.abonnements[i + 1];
  }
  client.nb_abonnements--;
}

void remove_abonne(Client client, Client param) {
  int id_client_in_abonnes = find_pseudo_in_subscriptions(param, client.pseudo);

  // Le pseudo donné en paramètre n'existe pas dans les abonnés du pseudo
  if (id_client_in_abonnes == -1) {
    printf("%s n'est pas dans les abonnés de %s\n", client.pseudo,
           param.pseudo);
    return;
  }

  // On enleve le client de la liste des abonnés
  for (int i = id_client_in_abonnes; i < client.nb_abonnes; i++) {
    param.abonnes[i] = param.abonnes[i + 1];
  }
  param.nb_abonnes--;
}

void list(int id_client) {
  Client client = clients[id_client];

  if (client.nb_abonnements == 0) {
    printf("Abonnements de %s : aucun\n", client.pseudo);
    write_answer(client, "aucun");
  } else {
    char request[(LG_PSEUDO + 1) * client.nb_abonnements];
    memset(request, 0, sizeof(request));
    printf("Abonnements de %s (%d) : \n", client.pseudo, client.nb_abonnements);
    for (int i = 0; i < client.nb_abonnements; i++) {
      strcat(request, client.abonnements[i]);
      strcat(request, "\n");
    }
    request[(LG_PSEUDO + 1) * client.nb_abonnements - 1] = '\0';
    printf("%s\n", request);
    write_answer(client, request);
  }
}

// TODO réponse au client
void post(int id_client, char *msg) {
  // // Si la liste de messages est pleine on double sa taille
  // if (client.nb_messages == client.size_messages) {
  //   client.size_messages *= 2;
  //   client.messages = (char **)realloc(client.messages,
  //                                      sizeof(char *) *
  //                                      client.size_messages);
  // }
  //
  // // On ajoute un message à la liste des messages du client
  // client.messages[client.nb_messages++] = msg;
}

// TODO réponse au client
void quit(int id_client) {
  for (int i = 0; i < NMAX_CLIENTS; i++) {
    if (clients[i].socket == clients[id_client].socket) {
      clients[i].socket = -1;
      clients[i].adresse = NULL;
      return;
    }
  }
}
