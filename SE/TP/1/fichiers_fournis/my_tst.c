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

int main() {
  while (1) {
    struct cmdline *l;
    int pid, status;
    int in, out;
    int fd[2];
    // int i = 0;

    printf("shell> ");
    l = readcmd();
    char **cmd = l->seq[0];
    pipe(fd);

    switch (fork()) {
    case -1:
      printf("Erreur\n");
      break;
    case 0:
      printf("%s\n", cmd[0]);
      close(fd[0]);
      dup2(fd[1], STDOUT_FILENO);
      close(fd[1]);
      execvp(cmd[0], cmd);
      // break;
    default:
      printf("Père\n");
      cmd = l->seq[1];
      switch (fork()) {
      case 0:
        close(0);
        close(fd[1]);
        dup2(fd[0], STDIN_FILENO);
        close(fd[0]);
        execvp(cmd[0], cmd);
      default:
        close(fd[0]);
        close(fd[1]);
        wait(NULL);
      }
    }

    // wait(NULL);
    //
    //   /* Exit : If input stream closed, normal termination */
    //   if (!l || strcmp(cmd[0], "exit") == 0) {
    //     printf("exit\n");
    //     exit(0);
    //   }
    //
    //   /* Syntax error: read another command */
    //   if (l->err) {
    //     printf("error: %s\n", l->err);
    //     continue;
    //   } else {
    //     // while (cmd != NULL) {
    //     pipe(fd);
    //     pid = fork();
    //
    //     /* Error when creating process */
    //     if (pid < 0) {
    //       perror("shell error: fork failed\n");
    //       exit(-1);
    //     }
    //     /* Child code */
    //     else if (pid == 0) {
    //       // SI in ET première commande
    //       // if (l->in) {
    //       //   in = open(l->in, O_RDONLY);
    //       //   dup2(in, STDIN_FILENO);
    //       //   close(in);
    //       // }
    //
    //       // Si out ET dernière commande
    //       // if (l->out) {
    //       //   out = open(l->out, O_WRONLY | O_CREAT, 777);
    //       //   dup2(out, STDOUT_FILENO);
    //       //   close(out);
    //       // }
    //
    //       close(fd[0]);
    //       dup2(fd[1], STDOUT_FILENO);
    //       close(fd[1]);
    //
    //       printf("Fils %s\n", cmd[0]);
    //
    //       if (execvp(cmd[0], cmd) == -1) {
    //         perror("shell error on execv\n");
    //         exit(-1);
    //       }
    //
    //     }
    //     /* Father code */
    //     else {
    //
    //       cmd = l->seq[1];
    //       // waitpid(pid, &status, 0);
    //       pid = fork();
    //
    //       if (pid < 0) {
    //         perror("shell error: fork failed\n");
    //         exit(-1);
    //       } else if (pid == 0) {
    //
    //         close(fd[1]);
    //         dup2(fd[0], STDIN_FILENO);
    //         close(fd[0]);
    //
    //         printf("Père %s\n", cmd[0]);
    //
    //         if (execvp(cmd[0], cmd) == -1) {
    //           perror("shell error on execv\n");
    //           exit(-1);
    //         }
    //       } else {
    //         wait(NULL);
    //       }
    //     }
    //
    //     // cmd = l->seq[++i];
    //     // }
    //   }
    // }
  }
  return 0;
}
