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
    int i, j, pid, status;
    int in, out;

    printf("shell> ");
    l = readcmd();
    char **cmd = l->seq[0];

    /* If input stream closed, normal termination */
    if (!l || strcmp(cmd[0], "exit") == 0) {
      printf("exit\n");
      exit(0);
    }

    if (l->err) {
      /* Syntax error, read another command */
      printf("error: %s\n", l->err);
      continue;
    } else {
      pid = fork();

      if (pid < 0) {
        perror("shell error: fork failed\n");
        exit(-1);
      } else if (pid == 0) {
        /* child code */
        if (l->in) {
          in = open(l->in, O_RDONLY);
          dup2(in, STDIN_FILENO);
        }
        if (l->out) {
          out = open(l->out, O_WRONLY | O_CREAT, 777);
          dup2(out, STDOUT_FILENO);
        }
        if (execvp(cmd[0], cmd) == -1) {
          perror("shell error on execv\n");
          exit(-1);
        }
      } else {
        /* father code */
        waitpid(pid, &status, 0);

        // if (l->in)
        //   printf("in: %s\n", l->in);
        // if (l->out)
        //   printf("out: %s\n", l->out);

        /* Display each command of the pipe */
        // for (i = 0; l->seq[i] != 0; i++) {
        //   char **cmd = l->seq[i];
        //   printf("seq[%d]: ", i);
        //   for (j = 0; cmd[j] != 0; j++) {
        //     printf("%s ", cmd[j]);
        //   }
        //   printf("\n");
        // }
      }
    }
  }
}
