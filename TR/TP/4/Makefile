CC=gcc
PROGS=client serveur

all: $(PROGS)

%.o: %.c %.h
	$(CC) -c $<

client: client.o
	$(CC) -o $@ $^

serveur: serveur.o
	$(CC) -o $@ $^

clean :
	rm *.o $(PROGS)
