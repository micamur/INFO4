CC=gcc
CFLAGS=-Wall -g

all: tst my_tst # shell

tst: tst.o readcmd.o

my_tst: my_tst.o readcmd.o

# shell: shell.o readcmd.o

clean:
	rm -f shell shell.o readcmd.o tst tst.o my_tst my_tst.o in* out*
