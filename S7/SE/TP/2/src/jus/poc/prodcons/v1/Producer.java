package jus.poc.prodcons.v1;

import java.io.IOException;

import jus.poc.prodcons.Message;
import jus.poc.prodcons.Options;

public class Producer extends Thread {

	private ProdConsBuffer buffPC; // buffer commun
	private int prodTime; // temps mis pour produire un Message
	private int idProd; // identifiant du Producer (utile pour débuguer)
	private int nbMsg; // nombre de messages restants à produire
	private int nbMsgTotal; // nombre total de messages à produire

	public Producer(ProdConsBuffer buff, int id, int prodTime, int minProd, int maxProd) throws IOException {
		this.prodTime = prodTime;

		nbMsg = minProd + (int) (Math.random() * (maxProd - minProd));
		buffPC = buff;
		idProd = id;
		nbMsgTotal = nbMsg;
	}

	/*
	 * Produit un message (cela prend un certain temps).
	 */
	public Message prod() {
		try {
			Thread.sleep(prodTime);
		} catch (InterruptedException e) {
			System.out.println("Prod sleep interrupted");
			e.printStackTrace();
		}
		if (Options.ECHO_PROD_PROD)
			System.out.println("> prod[" + idProd + "].prod : \"Message n°" + getNumMsg() + " produit par " + idProd
					+ "\" (n° global ~" + buffPC.totmsg() + ")");
		nbMsg--;
		return new Message("Message n°" + getNumMsg() + " produit par " + idProd);
	}

	@Override
	public void run() {
		// On produit des Messages tant qu'il en reste à produire
		while (nbMsg > 0) {
			buffPC.put(prod());
		}

		if (Options.ECHO_PROD_FINISHED)
			System.out.println("prod[" + idProd + "] fini.");
	}

	@Override
	public void start() {
		if (Options.ECHO_PROD_STARTED)
			System.out.println("prod[" + idProd + "] démarré.");
		super.start();
	}

	/*
	 * Renvoie le nombre de messages restants à produire
	 */
	public int getNbMsgTodo() {
		return nbMsg;
	}

	/*
	 * Renvoie le nombre total de messages à produire
	 */
	public int getNbMsgTotal() {
		return nbMsgTotal;
	}

	/*
	 * Renvoie le numéro du dernier message produit
	 */
	public int getNumMsg() {
		return nbMsgTotal - nbMsg;
	}

	/*
	 * Renvoie l'identifiant du Producer
	 */
	public int getProdId() {
		return idProd;
	}

}