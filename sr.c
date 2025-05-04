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
#define SEQSPACE 7      /* the min sequence space for GBN must be at least windowsize + 1 */
#define NOTINUSE (-1)   /* used to fill header fields that are not being used */


/*-->1 Addition of global array to track which packets are ACK and for buffer*/ 
static bool acked[SEQSPACE];
static struct pkt recv_buffer[SEQSPACE];
static bool received[SEQSPACE];





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
static int windowfirst, windowlast;    /* array indexes of the first/last packet awaiting ACK */
static int windowcount;                /* the number of packets currently awaiting an ACK */
static int A_nextseqnum;               /* the next sequence number to be used by the sender */

/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{
  struct pkt sendpkt;
  int i;

  /* if not blocked waiting on ACK */
  if ( windowcount < WINDOWSIZE) {
    if (TRACE > 1)
      printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");

    /* create packet */
    sendpkt.seqnum = A_nextseqnum;
    sendpkt.acknum = NOTINUSE;
    for ( i=0; i<20 ; i++ )
      sendpkt.payload[i] = message.data[i];
    sendpkt.checksum = ComputeChecksum(sendpkt);

    /* put packet in window buffer */
    /* windowlast will always be 0 for alternating bit; but not for GoBackN */
    windowlast = (windowlast + 1) % WINDOWSIZE;
    buffer[windowlast] = sendpkt;
    windowcount++;

    /* send out packet */
    if (TRACE > 0)
      printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
    tolayer3 (A, sendpkt);

    /* start timer if first packet in window */
    if (windowcount == 1)
      starttimer(A,RTT);

    /* get next sequence number, wrap back to 0 */
    A_nextseqnum = (A_nextseqnum + 1) % SEQSPACE;
  }
  /* if blocked,  window is full */
  else {
    if (TRACE > 0)
      printf("----A: New message arrives, send window is full\n");
    window_full++;
  }
}


/* called from layer 3, when a packet arrives for layer 4
   In this practical this will always be an ACK as B never sends data.
*/

/*-->2 MArking EVERY ACK individually*/   

void A_input(struct pkt packet)
{
  

  /* if received ACK is not corrupted */
  if (!IsCorrupted(packet)) {
    if (TRACE > 0)
      printf("----A: ACK %d received\n", packet.acknum);

    total_ACKs_received++;

    
    if (!acked[packet.acknum]) {
      acked[packet.acknum] = true;
      new_ACKs++;

      /* Remove ACKed packets from buffer*/
      while (windowcount > 0 && acked[buffer[windowfirst].seqnum]) {
        acked[buffer[windowfirst].seqnum] = false;
        windowfirst = (windowfirst + 1) % WINDOWSIZE;
        windowcount--;
      }

      stoptimer(A);
      if (windowcount > 0)
        starttimer(A, RTT);
    } else {
      if (TRACE > 0)
        printf("----A: Duplicate ACK received\n");
    }
  } else {
    if (TRACE > 0)
      printf("----A: Corrupted ACK received\n");
  }
}

/* called when A's timer goes off */

/*-->3 Modifying to send only UNACK packets*/
void A_timerinterrupt(void)
{int i;
  

  if (TRACE > 0){
    printf("----A: time out,resend packets!\n");
  }

  for ( i = 0; i < windowcount; i++) {
    int idx = (windowfirst + i) % WINDOWSIZE;
    int seq = buffer[idx].seqnum;

    if (!acked[seq]) {
      if (TRACE > 0)
        printf("----A: Resending packet %d\n", seq);
      tolayer3(A, buffer[idx]);
      packets_resent++;
    }
  }

    starttimer(A, RTT);
}



/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */


/*-->4 adding for loop to set every ACK to False*/



void A_init(void)
{
  int i;
  /* initialise A's window, buffer and sequence number */
  A_nextseqnum = 0;  /* A starts with seq num 0, do not change this */
  windowfirst = 0;
  windowlast = -1;   /* windowlast is where the last packet sent is stored.
		     new packets are placed in winlast + 1
		     so initially this is set to -1
		   */
  windowcount = 0;
  for ( i = 0; i < SEQSPACE; i++)
    acked[i] = false;
}



/********* Receiver (B)  variables and procedures ************/

static int expectedseqnum; /* the sequence number expected next by the receiver */
static int B_nextseqnum;   /* the sequence number for the next packets sent by B */


/* called from layer 3, when a packet arrives for layer 4 at B*/

/* --> 5 Modifying to accept out of order and buffer*/ 
void B_input(struct pkt packet)
{
  struct pkt ackpkt;
  int i;

  if (!IsCorrupted(packet)) {
    int seq = packet.seqnum;

    if (!received[seq]) {
      recv_buffer[seq] = packet;
      received[seq] = true;
    }

    /*Send ACK for received packet*/ 
    ackpkt.seqnum = B_nextseqnum;
    B_nextseqnum = (B_nextseqnum + 1) % 2;
    ackpkt.acknum = seq;
    for (i = 0; i < 20; i++)
      ackpkt.payload[i] = '0';
    ackpkt.checksum = ComputeChecksum(ackpkt);
    tolayer3(B, ackpkt);

    /*Deliver in-order packets to layer 5*/ 
    while (received[expectedseqnum]) {
      tolayer5(B, recv_buffer[expectedseqnum].payload);
      received[expectedseqnum] = false;
      expectedseqnum = (expectedseqnum + 1) % SEQSPACE;
    }
  } else {
    if (TRACE > 0)
      printf("----B: Corrupted packet, ignoring\n");
  }
}

/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */

/*-->  initiating with default false value*/
void B_init(void)
{int i;
  expectedseqnum = 0;
  B_nextseqnum = 1;
  for ( i = 0; i < SEQSPACE; i++)
    received[i] = false;
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
  