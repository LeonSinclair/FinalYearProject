include "../Channels.dfy"
module pipelineExcessReceives{ 


import opened Channels
//Testing staged pipeline with multiple different channels with different names
//Can be run on play.golang.org

method main(){
	var ch := new BinaryChannel<int>(Snd(Snd(Snd(Snd(Snd(End))))));
	var outch := new BinaryChannel<int>(Snd(Snd(Snd(Snd(Snd(End))))));
	var tmp_ep0 := ch.getPositiveEndpoint();
	generate(tmp_ep0);
	var tmp_ep1 := ch.getNegativeEndpoint();
	var tmp_ep2 := outch.getPositiveEndpoint();
	square(tmp_ep1, tmp_ep2);
	var tmp_ep3 := outch.getNegativeEndpoint();
	output(tmp_ep3);

}

method generate(ch: Endpoint<int>)
	modifies ch
	requires ch.st == Snd(Snd(Snd(Snd(Snd(End)))))
	requires ch.closed == false	{
	var i := 0;
	while i < 5 
		invariant 5-i == countSnd(ch.st){
		ch.send(i);
		i := i + 1;

	}

}

method square(ch: Endpoint<int>, outputch: Endpoint<int>)
	modifies ch, outputch
	requires ch.st == Rcv(Rcv(Rcv(Rcv(Rcv(End)))))
	requires outputch.st == Snd(Snd(Snd(Snd(Snd(End)))))
	requires ch.closed == false
	requires outputch.closed == false
	requires ch.canCloseChan == true{
	var i := 0;
	while i < 5 
		invariant 5-i == countRcv(ch.st)
		invariant 5-i == countSnd(outputch.st)
		invariant ch.closed == false
		invariant ch.canCloseChan == true
		invariant outputch.closed == false{
		var n := ch.receive();
		var sq := n * n;
		outputch.send(sq);
		i := i + 1;

	}
	ch.close();
}

method output(outch: Endpoint<int>)
	modifies outch
	requires outch.st == Rcv(Rcv(Rcv(Rcv(Rcv(End)))))
	requires outch.closed == false
	requires outch.canCloseChan == true
	ensures outch.closed == true{
	var i := 0;
	while i < 4
		invariant 5-i == countRcv(outch.st)
		invariant outch.closed == false
		invariant outch.canCloseChan == true{
		var x := outch.receive();
		print("Received: %d\n", x);
		i := i + 1;

	}
	outch.close();
}

}
