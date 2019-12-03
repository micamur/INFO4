package jus.poc.prodcons.v1;

import java.io.IOException;

import jus.poc.prodcons.Message;
import jus.poc.prodcons.Options;

public class Consumer extends Thread {

	private ProdConsBuffer buffPC; // buffer commun
	private int consTime; // temps mis pour lire un Message
	private int idCons; // identifiant du Consumer (utile pour débuguer)
	private int nbMsgCons; // nombre de messages consommés
	private volatile Boolean isInterrupted; // booléen qui indique si le programme est terminé

	public Consumer(ProdConsBuffer buff, int id, int consTime) throws IOException {
		this.consTime = consTime;

		buffPC = buff;
		this.idCons = id;
		nbMsgCons = 0;
		isInterrupted = false;
	}

	/*
	 * Lit un message (cela prend un certain temps).
	 */
	public void read(Message m) {
		try {
			Thread.sleep(consTime);
		} catch (InterruptedException e) {
			System.out.println("Read sleep interrupted");
			e.printStackTrace();
		}

		if (Options.ECHO_CONS_READ)
			System.out.println(
					"< cons[" + idCons + "].read : \"" + m.getMsg() + "\" (n° global " + buffPC.totmsgGet() + ")");
		nbMsgCons++;
	}

	/*
	 * Démarre un Consumer.
	 *
	 * Tant que le programme principal n'est pas terminé, il tente de lire.
	 */
	@Override
	public void run() {
		// On essaie en boucle de lire un Message
		while (true) {
			// On synchronise sur le booléen d'interruption
			synchronized (this.isInterrupted) {
				// Si le Consumer est interrompu on sort de la boucle infinie.
				if (isInterrupted) {
					break;
				}
				// Si le Consumer n'est pas interrompu et qu'il y a au moins un Message,
				// on lit un Message dans le buffer.
				if (!buffPC.isEmpty()) {
					read(buffPC.get());
				} else if (Options.ECHO_CONS_SLEEP) {
					System.out.println("cons[" + idCons + "] attend car buffer vide.");
				}
			}
		}
	}

	@Override
	public void start() {
		if (Options.ECHO_CONS_STARTED)
			System.out.println("cons[" + idCons + "] démarré.");
		super.start();
	}

	/*
	 * Renvoie le nombre de messages consommés par ce Consumer.
	 */
	public int getNbMsgCons() {
		return nbMsgCons;
	}

	/*
	 * Renvoie l'identifiant du Consumer
	 */
	public int getConsId() {
		return idCons;
	}

	@Override
	public void interrupt() {
		synchronized (this.isInterrupted) {
			this.isInterrupted = true;
			super.interrupt();
		}

		if (Options.ECHO_CONS_INTERRUPTED)
			System.out.println("cons[" + idCons + "] interrompu.");
	}

}