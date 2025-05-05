#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include "emulator.h"
#include "sr.h"

/* ******************************************************************
   Go Back N protocol.  Adapted from J.F.Kurose
   ALTERNATING BIT AND GO-BACK-N NETWORK EMULATOR: VERSION 1.2

   Network properties:
   - one way network delay averages five time units (longer if there
   are other messages in the channel for GBN), but can be larger
   - packets can be corrupted (either the header or the data portion)
   or lost, according to user-defined probabilities
   - packets will be delivered in the order in which they were sent
   (although some can be lost).

   Modifications:
   - removed bidirectional GBN code and other code not used by prac.
   - fixed C style to adhere to current programming style
   - added GBN implementation
**********************************************************************/

#define RTT  16.0       /* round trip time.  MUST BE SET TO 16.0 when submitting assignment */
#define WINDOWSIZE 6    /* the maximum number of buffered unacked packet
                          MUST BE SET TO 6 when submitting assignment */
#define SEQSPACE (2*WINDOWSIZE) /* Selective Repeat requires sequence space >= 2*WINDOWSIZE */
#define NOTINUSE (-1)   /* used to fill header fields that are not being used */


/*-->1 Addition of global array to track which packets are ACK and for buffer*/ 



/* generic procedure to compute the checksum of a packet.  Used by both sender and receiver
   the simulator will overwrite part of your packet with 'z's.  It will not overwrite your
   original checksum.  This procedure must generate a different checksum to the original if
   the packet is corrupted.
*/
int ComputeChecksum(struct pkt packet)
{
  int checksum = 0;
  int i;

  checksum = packet.seqnum;
  checksum += packet.acknum;
  for ( i=0; i<20; i++ )
    checksum += (int)(packet.payload[i]);

  return checksum;
}

bool IsCorrupted(struct pkt packet)
{
  if (packet.checksum == ComputeChecksum(packet))
    return (false);
  else
    return (true);
}


/********* Sender (A) variables and functions ************/

static struct pkt buffer[WINDOWSIZE];  /* array for storing packets waiting for ACK */
static bool acked[WINDOWSIZE];         /* tracks which packets in window have been ACKed */
static int windowbase;                 /* sequence number of first packet in window */
static int windowcount;                /* the number of packets currently awaiting an ACK */
static int A_nextseqnum;               /* the next sequence number to be used by the sender */

/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{struct pkt sendpkt;
  int i;
  int windowpos;

  /* if not blocked waiting on ACK */
  if (windowcount < WINDOWSIZE) {
    if (TRACE > 1)
      printf("----A: New message arrives, send window is not full, send new mesage to layer3!\n");

    /* create packet */
    sendpkt.seqnum = A_nextseqnum;
    sendpkt.acknum = NOTINUSE;
    for (i = 0; i < 20; i++)
      sendpkt.payload[i] = message.data[i];
    sendpkt.checksum = ComputeChecksum(sendpkt);

    /* put packet in window buffer */
    windowpos = A_nextseqnum % WINDOWSIZE;
    buffer[windowpos] = sendpkt;
    acked[windowpos] = false;
    windowcount++;

    /* send out packet */
    if (TRACE > 0)
      printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
    tolayer3(A, sendpkt);

    /* start timer for this packet if it's the first in window */
    if (windowcount == 1)
      starttimer(A, RTT);

    /* get next sequence number */
    A_nextseqnum = (A_nextseqnum + 1) % SEQSPACE;
  }
  else {
    if (TRACE > 0)
      printf("----A: New message arrives, send window is full\n");
    window_full++;
  }
}


/* called from layer 3, when a packet arrives for layer 4
   In this practical this will always be an ACK as B never sends data.
*/

/* MArking EVERY ACK individually*/   

void A_input(struct pkt packet)
{
  if (!IsCorrupted(packet)) {
    if (TRACE > 0) {
      printf("----A: uncorrupted ACK %d is received\n", packet.acknum);
      printf("----A: ACK %d is not a duplicate\n", packet.acknum);
    }
    total_ACKs_received++;

    /* Check if ACK is within current window */
    if ((windowbase <= packet.acknum && packet.acknum < windowbase + WINDOWSIZE) ||
        (windowbase + WINDOWSIZE > SEQSPACE && 
         (packet.acknum >= windowbase || packet.acknum < (windowbase + WINDOWSIZE) % SEQSPACE))) {
      
      /* Mark packet as ACKed */
      int windowpos = packet.acknum % WINDOWSIZE;
      if (!acked[windowpos]) {
        acked[windowpos] = true;
        new_ACKs++;
        
        /* If this is the base of the window, slide window forward */
        if (packet.acknum == windowbase) {
          while (windowcount > 0 && acked[windowbase % WINDOWSIZE]) {
            windowbase = (windowbase + 1) % SEQSPACE;
            windowcount--;
          }
          /* Restart timer if there are still unacked packets */
          stoptimer(A);
          if (windowcount > 0)
            starttimer(A, RTT);
        }
      }
    }
  }
  else {
    if (TRACE > 0)
      printf ("----A: corrupted ACK is received, do nothing!\n");
  }
}

/* called when A's timer goes off */

/*-->3 Modifying to send only UNACK packets*/
void A_timerinterrupt(void)
{int i;
  if (TRACE > 0)
  printf("----A: timeout, resending all unacked packets in window\n");

/* Resend all unacked packets in window */
for (i = 0; i < WINDOWSIZE; i++) {
  int current_seq = (windowbase + i) % SEQSPACE;
  int windowpos = current_seq % WINDOWSIZE;
  
  if (!acked[windowpos] && current_seq < A_nextseqnum) {
    if (TRACE > 0)
      printf("---A: resending packet %d\n", buffer[windowpos].seqnum);

    tolayer3(A, buffer[windowpos]);
    packets_resent++;
  }
}

/* Restart timer */
starttimer(A, RTT);
}



/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */


/*-->4 adding for loop to set every ACK to False*/



void A_init(void)
{
  int i;
  
  A_nextseqnum = 0;
  windowbase = 0;
  windowcount = 0;
  for ( i = 0; i < WINDOWSIZE; i++) {
    acked[i] = false;
  }
}



/********* Receiver (B)  variables and procedures ************/

static bool received[SEQSPACE];        /* tracks which packets have been received */
static int expectedseqnum;             /* the sequence number expected next by the receiver */
static int B_nextseqnum;               /* the sequence number for the next packets sent by B */
          
int B_total_packets_received = 0;
/* called from layer 3, when a packet arrives for layer 4 at B*/

/* --> 5 Modifying to accept out of order and buffer*/ 
void B_input(struct pkt packet)
{struct pkt sendpkt;
  int i;
  bool packet_accepted = false;

  if (!IsCorrupted(packet)) {
    /* Mark packet as received if it's within our expected window */
    if ((expectedseqnum <= packet.seqnum && packet.seqnum < expectedseqnum + WINDOWSIZE) ||
        (expectedseqnum + WINDOWSIZE > SEQSPACE &&
         (packet.seqnum >= expectedseqnum || packet.seqnum < (expectedseqnum + WINDOWSIZE) % SEQSPACE))) {
      received[packet.seqnum] = true;
      packet_accepted = true;
      packets_received++; 
    }

    /* Deliver all in-order packets we have */
    while (received[expectedseqnum]) {
      if (TRACE > 0)
        printf("----B: packet %d is correctly received, send ACK!\n", packet.seqnum);
      
      tolayer5(B, packet.payload);
      received[expectedseqnum] = false;
      expectedseqnum = (expectedseqnum + 1) % SEQSPACE;
    }
  }

  /* Send ACK for the highest in-order packet */
  sendpkt.acknum = (expectedseqnum - 1 + SEQSPACE) % SEQSPACE;
  sendpkt.seqnum = B_nextseqnum;
  B_nextseqnum = (B_nextseqnum + 1) % 2;

  for (i = 0; i < 20; i++)
    sendpkt.payload[i] = '0';

  sendpkt.checksum = ComputeChecksum(sendpkt);

  /* Send ACK */
  tolayer3(B, sendpkt);
  
  if (TRACE > 1 && packet_accepted)
  {}
    /*printf("----B: packet %d accepted (total received: %d)\n", packet.seqnum, packets_received);*/
    

}

/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */

/*-->  initiating with default false value*/
void B_init(void)
{   int i;
  expectedseqnum = 0;
  B_nextseqnum = 1;
  packets_received = 0;  
  for (i = 0; i < SEQSPACE; i++) {
    received[i] = false;
  }
}

/******************************************************************************
 * The following functions need be completed only for bi-directional messages *
 *****************************************************************************/

/* Note that with simplex transfer from a-to-B, there is no B_output() */
void B_output(struct msg message)
{
}

/* called when B's timer goes off */
void B_timerinterrupt(void)
{
}
  