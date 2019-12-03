#include "client.h"

/*
Valeur globale contenant le numéro de socket.
Elle est globale car on l'utilise souvent et que ce sera la même pendant toute
l'exécution du programme. La passer en paramètre alourdirait les appels de
fonction inutilement.
*/
int num_socket = 0;

int main(int argc, char *argv[]) {

  char *serveur = SERVEUR_DEFAUT; /* serveur par defaut */
  char *service = SERVICE_DEFAUT; /* num de service par defaut (no de port) */

  /* Permet de passer un nombre de parametre variable a l'executable */
  switch (argc) {
  case 1: /* arguments par defaut */
    printf("serveur par defaut: %s\n", serveur);
    printf("service par defaut: %s\n", service);
    break;
  case 2: /* serveur renseigne  */
    serveur = argv[1];
    printf("service par defaut: %s\n", service);
    break;
  case 3: /* serveur, service renseignes */
    serveur = argv[1];
    service = argv[2];
    break;
  default:
    printf("Usage:client serveur(nom ou @IP)  service (nom ou port) \n");
    exit(1);
  }

  /* serveur est le nom (ou l'adresse IP) auquel le client va acceder */
  /* service le numero de port sur le serveur correspondant au  */
  /* service desire par le client */

  client_appli(serveur, service);
}

/*****************************************************************************/

/*
Remplace la ligne précédement affiché par la ligne string en couleur :
'R' seras ecris en rouge, 'G' en vert, etc.
*/
void string_to_color(char *string) {
  // On retourne a la ligne précédente
  gotoprevline(1);

  // On l'efface
  clearline();

  // On affiche les caractères de la bonne couleur
  for (int i = 0; i < strlen(string); i++) {
    switch (string[i]) {
    case 'R':
      printf("%sR", RED);
      break;

    case 'G':
      printf("%sG", GREEN);
      break;

    case 'Y':
      printf("%sY", YELLOW);
      break;

    case 'B':
      printf("%sB", BLUE);
      break;

    case 'F':
      printf("%sF", FUSCHIA);
      break;

    case 'W':
      printf("%sW", WHITE);
      break;

    case 'P':
      printf("%sP", PURPLE);
      break;

    case 'O':
      printf("%sO", ORANGE);
      break;

    default:
      printf("%s%c", RESET, string[i]);
      break;
    }
  }
  printf("%s\t", RESET);
}

/*
Transforme un entier nb < 99 en une chaine de caractère
*/
void itoa(int nb, char *str) {
  // Si le nombre est supérieur a 10 (et implicitement inférieur a 99) alors on
  // a deux caractères
  if (nb >= 10) {
    str[0] = nb / 10 + '0';
    str[1] = nb % 10 + '0';
    str[2] = '\0';
  }
  // Le nombre est inférieur a 10 donc il suffit de convertir le chiffre en
  // caractère
  else {
    str[0] = nb + '0';
    str[1] = '\0';
  }
}

/*
Renvoie 1 si le message est de bonne taille et est composé uniquement de lettres
autorisées 0 sinon
*/
int msg_is_correct(char *msg, int n) {
  if (strlen(msg) != n)
    return 0;

  int i;
  for (i = 0; i < n; i++) {
    if (msg[i] != 'R' && msg[i] != 'Y' && msg[i] != 'G' && msg[i] != 'B' &&
        msg[i] != 'O' && msg[i] != 'W' && msg[i] != 'P' && msg[i] != 'F')
      return 0;
  }

  return 1;
}

/*
Récupère un guess donné par l'utilisateur et l'envoie au serveur
*/
void guess(int n) {
  char guess[99];
  scanf("%s", guess);
  // Une fois la chaîne récupéré on la remplace instanément en la même chaîne
  // mais en couleurs
  string_to_color(guess);

  // Sécurité si la chaîne est trop longue ou trop courte par rapport à la
  // taille n choisie en début de partie
  while (!msg_is_correct(guess, n)) {
    printf("Message de longueur incorect ou comportant des couleurs "
           "inexistantes\n");
    scanf("%s", guess);
    string_to_color(guess);
  }

  // Indication pour le serveur qu'il s'agit d'un Guess avec la lettre G comme
  // premier caractère du paquet
  char msg[100] = "G";
  strcat(msg, guess);
  // Envoie du message au Serveur
  // h_writes(num_socket, msg, strlen(msg) + 1);
}

void game() {
  // 1. Début du jeu, on récupère la taille du message à décoder que
  // l'utilisateur souhaite
  printf("Quel est la taille du mesage que vous souhaitez décoder ? [1, 98] "
         "(facile = 3, moyen = 5, difficile = 8)\n");
  int n;
  scanf("%d", &n);

  while (n < 1 || n > 98) {
    printf("Interdiction d'avoir une taille de message hors de l'intervalle "
           "[1, 98]\n");
    printf("Quel est la taille du mesage que vous souhaitez décoder ? [1, 98] "
           "(facile = 3, moyen = 5, difficile = 8)\n");
    scanf("%d", &n);
  }

  // 2. Envoie au serveur d'un paquet "N" contenant la taille des message à
  // décodé choisie par l'utilisateur
  char msg[4] = "N";
  char tmp[3];
  itoa(n, tmp);
  strcat(msg, tmp);
  // h_writes(num_socket, msg, strlen(msg) + 1);

  int QUIT = 0;
  // 3. Boucle principale du jeu
  while (!QUIT) {
    char raw[100];
    // On lis un paquet envoyé par le Serveur
    read(num_socket, raw, 100);
    switch (raw[0]) {
    /*
    Si c'est un paquet "O" (OK) alors on écris le message de début de jeu
    et on demande à l'utilisateur de faire une première prédiction
    */
    case 'O':
      printf("Entrez une chaîne de %d couleurs parmi : %sR %sY %sG %sB %sO %sW "
             "%sP %sF%s\n",
             n, RED, YELLOW, GREEN, BLUE, ORANGE, WHITE, PURPLE, FUSCHIA,
             RESET);
      guess(n);
      break;
    /*
    Si c'est un paquet "W" (Win) alors on indique que la partie est terminé
    et on sort de la boucle principale
    */
    case 'W':
      printf("Bravo, vous avez gagné en %d essais !\n", atoi(&(raw[1])));
      QUIT = 1;
      break;
    /*
    Si c'est un paquet "A" (Answer) alors on affiche la réponse donnée par le
    serveur (qui est déjà formaté) et on demonde à l'utilisateur la prochaine
    prédiction
    */
    case 'A':
      printf("%s\n", &(raw[1]));
      guess(n);
      break;
    default:
      printf("Default, anormal\n");
      break;
    }
  }

  // 4. La partie est terminée, on donne le choix à l'utilisateur de recommencer
  printf("Souhaitez vous recommencer ? (O : Oui / N : Non)\n");
  while ((getchar()) != '\n')
    ;
  char c = getchar();
  // Si l'utilisateur souhaite recommencer on relance une nouvelle partie
  if (c == 'O' || c == 'o')
    game();

  char msg2[2] = "Q";
  // h_writes(num_socket, msg2, strlen(msg) + 1);
  return;
}

/* procedure correspondant au traitement du client de votre application */
void client_appli(char *serveur, char *service) {
  // Création de la socket
  num_socket = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);

  // Connection au serveur
  const struct sockaddr_in padr_serveur;
  // adr_socket(service, serveur, SOCK_STREAM, &padr_serveur);
  connect(num_socket, (struct sockaddr *)&padr_serveur, sizeof(struct sockaddr_in));

  char demande_client;
  scanf("%c", &demande_client);
  user_choice(demande_client);

  // Fermeture de la connexion
  close(num_socket);
}

/*****************************************************************************/

void user_choice(char c) {
  switch (c) {
  // Subscribe : s’abonner à un compte en donnant le nom d’un pseudo
  case 'S':
    subscribe();
    break;
  // Unsubscribe : se désabonner d'un compte
  case 'U':
    unsubscribe();
    break;
  // List : lister tous les pseudos auxquels il est abonné
  case 'L':
    list();
    break;
  // Post : publier un message < 20 caractères à ses abonnés
  case 'P':
    post();
    break;
  // Quit : quitter l’application
  case 'Q':
    quit();
    break;
  }
}

void subscribe() {}
void unsubscribe() {}
void list() {}
void post() {}
void quit() {}
