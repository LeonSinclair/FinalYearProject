//Code written by Dr. Vasileios Koutavas
module Channels {
export reveals Branch, SessionT, subst, complement, countSnd, countRcv, multiSnd, multiRcv, Endpoint, BinaryChannel, ManyProducersOneConsumerChannel

/* Session Types Grammar defined as datatypes.
	The basic datatype is SessionT. The Branch datatype is used for choices
*/

datatype Branch =
	  Left
	| Right

datatype SessionT =
	  End
	| Snd(next : SessionT)
	| Rcv(next : SessionT)
	| InCh(inLeft : string, leftNext : SessionT, inRight : string, rightNext : SessionT)
	| ExCh(exLeft : string, leftNext : SessionT, exRight : string, rightNext : SessionT)
	| Rec(recNext : SessionT)
	| Loop(debruijn : nat)

// de Bruijn substitution of the outermost bound variable.
function subst(inst : SessionT, whatst : SessionT, level: int) : SessionT{
	match inst {
		case End => End
		case Snd(n) => Snd(subst(n, whatst, level))
		case Rcv(n) => Rcv(subst(n, whatst, level))
		case InCh(l, ln, r, rn) => InCh(l, subst(ln, whatst, level), r, subst(rn, whatst, level))
		case ExCh(l, ln, r, rn) => ExCh(l, subst(ln, whatst, level), r, subst(rn, whatst, level))
		case Rec(n) => Rec(subst(n, whatst, level+1))
		case Loop(i) => if (i == level) then whatst else Loop(i)
	}
}
// Given a session type this method returns its complement
function complement(st : SessionT) : SessionT {
	match st {
		case End => End
		case Snd(n) => Rcv(complement(n))
		case Rcv(n) => Snd(complement(n))
		case InCh(l, ln, r, rn) => ExCh(l, complement(ln), r, complement(rn))
		case ExCh(l, ln, r, rn) => InCh(l, complement(ln), r, complement(rn))
		case Rec(n) => Rec(complement(n))
		case Loop(i) => Loop(i)
	}
}
function countSnd(st : SessionT): nat {
        if (st.Snd?) then
                countSnd(st.next) + 1
        else if (st.End?) then
                0
        else
                1000000000 // some very large number, out of the bounds of our loops
}
function countRcv(st : SessionT): nat {
        if (st.Rcv?) then
                1 + countRcv(st.next)
        else if (st.End?) then
                0
        else
                1000000000 // some very large number, out of the bounds of our loops
}
function multiSnd(num : nat): (result:SessionT)
	ensures num == countSnd(result)
{
	if num == 0 then End
	else Snd(multiSnd(num-1))
}
function multiRcv(num : nat): (result:SessionT)
	ensures num == countRcv(result)
{
	if num == 0 then End
	else Rcv(multiRcv(num-1))
}

class Endpoint<T> {
	ghost var st : SessionT;
	ghost var closed : bool;
	ghost var canCloseChan : bool

	constructor (stype : SessionT)
	//modifies `st, `closed
	ensures st == stype
	ensures closed == false

	predicate Finished()
	reads `st
	{
		st.End?
	}

	method send(val : T)
	modifies `st
	requires st.Snd?
	ensures st == old(st).next;

	method receive() returns (val: T)
	modifies `st
	requires st.Rcv?
	ensures st == old(st).next;

	method selectCh(branch : Branch)
	modifies `st
	requires st.InCh? 
	ensures branch.Left? ==> st == old(st).leftNext
	ensures branch.Right? ==> st == old(st).rightNext


	method offerCh() returns (branch : Branch)
	modifies `st
	requires st.ExCh?
	ensures branch.Left? ==> st == old(st).leftNext
	ensures branch.Right? ==> st == old(st).rightNext
	
	method unfoldRec()
	modifies `st
	requires st.Rec?
	ensures st == subst(old(st).recNext, old(st), 0)

	method close()
	modifies `closed
	requires canCloseChan && closed == false
	requires st == End
	ensures closed == true

}

class BinaryChannel<T> {

	var st : SessionT;
	var positiveEndpUsed : bool;
	var negativeEndpUsed : bool;

	constructor (stype : SessionT)
	//modifies `st
	//modifies `positiveEndpUsed
	//modifies `negativeEndpUsed
	ensures st == stype
	ensures positiveEndpUsed == false
	ensures negativeEndpUsed == false

	method getPositiveEndpoint() returns (result: Endpoint<T>)
	modifies `positiveEndpUsed
	requires positiveEndpUsed == false
	ensures fresh(result)
	ensures positiveEndpUsed == true
	ensures result.st == st
	ensures result.canCloseChan == false
	ensures result.closed == false


	method getNegativeEndpoint() returns (result: Endpoint<T>)
	modifies `negativeEndpUsed
	requires negativeEndpUsed == false
	ensures fresh(result)
	ensures negativeEndpUsed == true
	ensures result.st == complement(st)
	ensures result.canCloseChan == true
	ensures result.closed == false
	



}

class ManyProducersOneConsumerChannel<T> {


	var numOfProducers : nat;
	var numOfSendsPerProducer : nat;
	// this is the endpoint of the consumer
	var consumerEndpUsed : bool;
	var producerEndpUsed : nat;

	constructor (nOfProducers:nat, nOfSendsPerProducer: nat)
	ensures nOfSendsPerProducer == numOfSendsPerProducer
	ensures nOfProducers == numOfProducers
	ensures consumerEndpUsed == false
	ensures producerEndpUsed == 0

	// these are the producers
	method getPositiveEndpoint() returns (result: Endpoint<T>)
	modifies `numOfProducers
	requires numOfProducers > producerEndpUsed
	ensures producerEndpUsed == old(producerEndpUsed) + 1
	ensures fresh(result)
	ensures result.st == multiSnd(numOfSendsPerProducer)
	ensures result.canCloseChan == false
	ensures result.closed == false

	// this is the consumer
	// - can be called only once
	// - must be called when all producers are spawned
	method getNegativeEndpoint() returns (result: Endpoint<T>)
	modifies `consumerEndpUsed
	// this endpoint can be used only once
	requires consumerEndpUsed == false
	requires numOfProducers == producerEndpUsed
	ensures consumerEndpUsed == true
	ensures fresh(result)
	ensures result.st == multiRcv(numOfProducers * numOfSendsPerProducer)
	ensures result.canCloseChan == true
	ensures result.closed == false
	



}


}