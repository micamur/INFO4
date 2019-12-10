package jus.poc.prodcons.v2;

import java.util.concurrent.Semaphore;

import jus.poc.prodcons.IProdConsBuffer;
import jus.poc.prodcons.Message;
import jus.poc.prodcons.Options;

public class ProdConsBuffer implements IProdConsBuffer {

	private Message[] buff; // tableau contenant les Messages
	private int nfree; // nombre de places libres dans le buffer
	private int in, out; // indices où mettre/prendre le prochain Message
	private int nbMsgTotalPut; // nombre total de Messages mis dans le buffer
	private int nbMsgTotalGet; // nombre total de Messages pris dans le buffer
	private Semaphore sGet;
	private Semaphore sPut;

	public ProdConsBuffer(int n) {
		nfree = n;
		buff = new Message[nfree];
		out = 0;
		in = 0;
		nbMsgTotalPut = 0;
		nbMsgTotalGet = 0;
		sGet = new Semaphore(1);
		sPut = new Semaphore(1);
	}

	@Override
	public void put(Message m) {
		try {
			sPut.acquire();
			synchronized (this) {
				while (isFull()) {
					try {
						wait();
					} catch (InterruptedException e) {
						System.out.println("Put wait interrupted");
						e.printStackTrace();
					}
				}
				nfree--;
				buff[in] = m;
				in = increment(in);
				nbMsgTotalPut++;
				if (Options.ECHO_PUT)
					System.out.println("> put : nfree = " + nfree() + " et nmsg = " + nmsg() + " (total = "
							+ (nfree() + nmsg()) + ")");
				notifyAll();
			}

			sPut.release();
		} catch (InterruptedException e1) {
			e1.printStackTrace();
		}
	}

	@Override
	public Message get() {
		Message m = null;
		try {
			sGet.acquire();
			synchronized (this) {
				while (isEmpty()) {
					try {
						wait();
					} catch (InterruptedException e) {
						System.out.println("Get wait interrupted");
						e.printStackTrace();
					}
				}
				nfree++;
				m = buff[out];
				out = increment(out);
				nbMsgTotalGet++;
				if (Options.ECHO_GET)
					System.out.println("< get : nfree = " + nfree() + " et nmsg = " + nmsg() + " (total = "
							+ (nfree() + nmsg()) + ")");
				notifyAll();
			}

			sGet.release();
		} catch (InterruptedException e1) {
			e1.printStackTrace();
		}
		return m;
	}

	@Override
	public int nmsg() {
		return buff.length - nfree();
	}

	@Override
	public int totmsg() {
		return nbMsgTotalPut;
	}

	/*
	 * Renvoie le nombre total de messages pris dans le buffer depuis sa création.
	 */
	public int totmsgGet() {
		return nbMsgTotalGet;
	}

	/*
	 * Incrémente un indice du buffer de manière circulaire.
	 */
	private int increment(int x) {
		return (x + 1) % buff.length;
	}

	/*
	 * Renvoie le nombre de places libres dans le buffer.
	 */
	public int nfree() {
		return nfree;
	}

	/*
	 * Renvoie vrai si le buffer est vide, faux sinon.
	 */
	public boolean isEmpty() {
		return nmsg() == 0;
	}

	/*
	 * Renvoie vrai si le buffer est plein, faux sinon.
	 */
	public boolean isFull() {
		return nfree() == 0;
	}
	
	/* Inutilisée dans V2 */
	@Override
	public Message[] get(int n) throws InterruptedException {
		return null;
	}

}