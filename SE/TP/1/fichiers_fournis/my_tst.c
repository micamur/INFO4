/*
 * Copyright (C) 2002, Simon Nieuviarts
 */

#include "readcmd.h"
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

// Close both ends of a pipe
void close_both(int fd[2]) {
  close(fd[0]);
  close(fd[1]);
}

// Duplicate STDIN
void dup2IN(int fd[2]) {
  close(fd[1]);
  dup2(fd[0], 0); // stdin
  close_both(fd);
}

// Duplicate STDOUT
void dup2OUT(int fd[2]) {
  close(fd[0]);
  dup2(fd[1], 1); // stdout
  close_both(fd);
}

// Redirect STDIN (<)
void redirectIN(struct cmdline *l) {
  int in = open(l->in, O_RDONLY);
  dup2(in, 0); // stdin
  close(in);
}

// Redirect STDOUT (>)
void redirectOUT(struct cmdline *l) {
  int out = open(l->out, O_WRONLY | O_CREAT | O_TRUNC, 0666);
  dup2(out, 1); // stdout
  close(out);
}

// Count the number of commands in seq
int countCommands(struct cmdline *l) {
  int i = 0;
  while (l->seq[i] != NULL)
    i++;
  return i;
}

// Returns true if the current cmd is before the last one
int isBeforeLastCmd(int cmdCur, int nbCommands) {
  return cmdCur < nbCommands - 1;
}

void execCmd(struct cmdline *l, int cmdCur) {
  if (execvp(l->seq[cmdCur][0], l->seq[cmdCur]) == -1) {
    perror("shell error on execv\n");
    exit(-1);
  }
}

// Returns true if the current cmd is before the last one
int isLastCmd(int cmdCur, int nbCommands) { return cmdCur == nbCommands - 1; }

int main() {
  while (1) {
    int pid, nbCommands;
    struct cmdline *l;

    /* Begin program: prompt and read */
    printf("shell> ");
    l = readcmd();
    char **cmd = l->seq[0];

    /* Exit : If input stream closed, normal termination */
    if (!l || strcmp(cmd[0], "exit") == 0) {
      printf("exit\n");
      exit(0);
    }

    /* Syntax error: read another command */
    if (l->err) {
      printf("error: %s\n", l->err);
      continue;
    }

    /* Normal: no syntax error */
    else {
      nbCommands = countCommands(l);

      // Tableau contenant tous les descripteurs de fichiers
      int fd[nbCommands - 1][2];
      // Permet de connaitre l'indice de la commande courante
      int cmdCur = 0;
      // Initialisé à 1 pour rentrer dans le while
      pid = 1;

      // seul le père peut boucler
      // et le père passe dans la boucle pour le nb de commande dans la sequence
      while (pid && cmdCur < nbCommands) {
        // Création des pipes dont on aura besoin
        if (isBeforeLastCmd(cmdCur, nbCommands)) {
          pipe(fd[cmdCur]);
        }

        // Création des enfants
        pid = fork();

        /* Père */
        if (pid != 0) {
          // on saute la première commande
          if (cmdCur > 0) {
            // on ferme le pipe precedent
            close_both(fd[cmdCur - 1]);
          }
          // on passe à la commande suivante
          cmdCur++;
        }
      }

      /* Fils */
      if (pid == 0) {
        // Redirection en entrée
        if (l->in) {
          redirectIN(l);
        }
        // Toutes les commandes sauf la première :
        // on récupère la sortie précédente dans l'entrée courante
        if (cmdCur != 0) {
          dup2IN(fd[cmdCur - 1]);
        }

        // Redirection de la sortie
        if (l->out) {
          redirectOUT(l);
        }
        // Toutes les commandes sauf la dernière :
        // on récupère la sortie courante dans l'entrée
        if (!isLastCmd(cmdCur, nbCommands)) {
          dup2OUT(fd[cmdCur]);
        }

        // On execute la commande courante
        execCmd(l, cmdCur);
      }

      /* Père */
      else {
        // On attend les enfants
        for (int i = 0; i < nbCommands; ++i) {
          wait(NULL);
        }
      }
    }
  }
  return 0;
}
