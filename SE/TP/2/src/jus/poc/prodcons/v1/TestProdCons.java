package jus.poc.prodcons.v1;

import java.io.IOException;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Properties;

import jus.poc.prodcons.Options;

public class TestProdCons {

	public static void main(String[] args) throws IOException {
		
		int totMsgGoal = 0; // nombre de messages total à produire et lire

		// On charge le fichier d'options
		Properties properties = new Properties();
		properties.loadFromXML(TestProdCons.class.getClassLoader().getResourceAsStream("options.xml"));
		// - options générales :
		int nProd = Integer.parseInt(properties.getProperty("nProd"));
		int nCons = Integer.parseInt(properties.getProperty("nCons"));
		int bufSz = Integer.parseInt(properties.getProperty("bufSz"));
		// - options des Producers :
		int prodTime = Integer.parseInt(properties.getProperty("prodTime"));
		int minProd = Integer.parseInt(properties.getProperty("minProd"));
		int maxProd = Integer.parseInt(properties.getProperty("maxProd"));
		// - option des Consumers :
		int consTime = Integer.parseInt(properties.getProperty("consTime"));

		// Initialisation des tableaux
		ProdConsBuffer buff = new ProdConsBuffer(bufSz);
		Producer[] prod = new Producer[nProd];
		Consumer[] cons = new Consumer[nCons];
		LinkedList<Thread> prodCons = new LinkedList<Thread>();

		// Création des Producers + initialisation du nombre de messages total
		for (int i = 0; i < nProd; i++) {
			prod[i] = new Producer(buff, i, prodTime, minProd, maxProd);
			prodCons.add(prod[i]);
			totMsgGoal += prod[i].getNbMsgTotal();
		}

		if (Options.ECHO_SUMMARY) {
			System.out.println(totMsgGoal + " messages, " + nProd + " producteurs et " + nCons + " consommateurs.");
			System.out.println("Buffer de taille " + bufSz + ", prodTime = " + prodTime + ", consTime = " + consTime + ".");
		}

		// Création des Consumers
		for (int i = 0; i < nCons; i++) {
			cons[i] = new Consumer(buff, i, consTime);
			prodCons.add(cons[i]);
		}

		// On mélange les tableaux de Consumers et de Producers
		Collections.shuffle(prodCons);
		for (Iterator<Thread> iterator = prodCons.iterator(); iterator.hasNext();) {
			iterator.next().start();
		}
		prodCons = null;

		// Une fois tous les Threads lancés, on attend la fin de tous les Producers
		for (int i = 0; i < nProd; i++) {
			try {
				prod[i].join();
			} catch (InterruptedException e) {
				System.out.println("Join interrupted prod[" + i + "]");
				e.printStackTrace();
			}
		}

		if (Options.ECHO_ALL_PROD_FINISHED)
			System.out.println("Les " + nProd + " producteurs ont terminé.");

		// Une fois tous les Messages produits, on attend qu'ils soient tous lus
		while (buff.totmsg() != totMsgGoal) {
		}

		// Une fois tous les Messages lus, on termine les Consumers
		for (int i = 0; i < nCons; i++) {
			cons[i].interrupt();
		}

		if (Options.ECHO_ALL_CONS_INTERRUPTED) {
			System.out.println("Les " + nCons + " consommateurs ont été interrompus.");
			System.out.println("Les " + totMsgGoal + " messages ont été produits et lus.");
		}

		return;

	}

}
