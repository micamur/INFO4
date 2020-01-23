package jus.poc.prodcons.v3;

import java.io.IOException;

import jus.poc.prodcons.Message;
import jus.poc.prodcons.Options;

public class Consumer extends Thread {

	private ProdConsBuffer buffPC; // buffer commun
	private int consTime; // temps mis pour lire un Message
	private int idCons; // identifiant du Consumer (utile pour débuguer)
	private int nbMsgCons; // nombre de messages consommés

	public Consumer(ProdConsBuffer buff, int id, int consTime) throws IOException {
		this.consTime = consTime;

		buffPC = buff;
		this.idCons = id;
		nbMsgCons = 0;
		setDaemon(true);
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
			read(buffPC.get());
		}

//		if (Options.ECHO_CONS_FINISHED)
//			System.out.println("cons[" + idCons + "] fini.");
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

}