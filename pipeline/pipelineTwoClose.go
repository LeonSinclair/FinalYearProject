//?include "../Channels.dfy"
package main

//?import opened Channels
//Testing staged pipeline with multiple different channels with different names
//Can be run on play.golang.org
import (
	"fmt"
)

func main() {
	ch := make(chan int /*?Snd(Snd(Snd(Snd(Snd(End)))))?*/)
	outch := make(chan int /*?Snd(Snd(Snd(Snd(Snd(End)))))?*/)
	go generate(ch /*+*/)
	go square(ch /*-*/, outch /*+*/)
	output(outch /*-*/)

}

func generate(ch chan int) {
	/*^modifies ch
	requires ch.st == Snd(Snd(Snd(Snd(Snd(End)))))
	requires ch.closed == false	>*/
	for i := 0; i < 5; i = i + 1 {
		/*^invariant 5-i == countSnd(ch.st)>*/
		ch <- i
	}
	close(ch)

}

func square(ch chan int, outputch chan int) {
	/*^modifies ch, outputch
	requires ch.st == Rcv(Rcv(Rcv(Rcv(Rcv(End)))))
	requires outputch.st == Snd(Snd(Snd(Snd(Snd(End)))))
	requires ch.closed == false
	requires outputch.closed == false
	requires ch.canCloseChan == true>*/
	for i := 0; i < 5; i = i + 1 {
		/*^invariant 5-i == countRcv(ch.st)
		invariant 5-i == countSnd(outputch.st)
		invariant ch.closed == false
		invariant ch.canCloseChan == true
		invariant outputch.closed == false>*/
		n := <-ch
		sq := n * n
		outputch <- sq
	}
	close(ch)
}

func output(outch chan int) {
	/*^modifies outch
	requires outch.st == Rcv(Rcv(Rcv(Rcv(Rcv(End)))))
	requires outch.closed == false
	requires outch.canCloseChan == true
	ensures outch.closed == true>*/
	for i := 0; i < 5; i = i + 1 {
		/*^invariant 5-i == countRcv(outch.st)
		invariant outch.closed == false
		invariant outch.canCloseChan == true>*/
		x := <-outch
		fmt.Printf("Received: %d\n", x)
	}
	close(outch)
}
