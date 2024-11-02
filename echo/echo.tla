-------------------------- MODULE echo --------------------------

EXTENDS Integers, Sequences, TLC
(* --algorithm echo

variables
  i = 0;
  p1 = "p1";
  p2 = "p2";
  network = [p1 |-> <<>>, p2 |-> <<>>];

define
  MessageEchoed == 
  /\ Len(network[p1]) <= 1
  /\ Len(network[p2]) <= 1

  SendReceiveResponse == 
  [](Len(network[p1]) > 0 => <> (Len(network[p2]) > 0))
end define;

macro send(to, msg) begin
  network[to] := Append(network[to], msg);
end macro;

macro receive(p, buffer) begin
  await Len(network[p]) > 0;
  buffer := Head(network[p]);
  network[p] := Tail(@);
end macro;

process process1 = 1
variable response;
begin
  SendToProcess2:
    send(p2, "hello");
  ReceiveFromProcess2:
    receive(p2, response);
end process;

process process2 = 2
variable buffer;
begin
  ReceiveFromProcess1:
    receive(p1, buffer);
    SendToProcess1:
      send(p1, buffer);
    goto ReceiveFromProcess1;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "55e24131" /\ chksum(tla) = "44d0345a")
CONSTANT defaultInitValue
VARIABLES pc, i, p1, p2, network

(* define statement *)
MessageEchoed ==
/\ Len(network[p1]) <= 1
/\ Len(network[p2]) <= 1

SendReceiveResponse ==
[](Len(network[p1]) > 0 => <> (Len(network[p2]) > 0))

VARIABLES response, buffer

vars == << pc, i, p1, p2, network, response, buffer >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ i = 0
        /\ p1 = "p1"
        /\ p2 = "p2"
        /\ network = [p1 |-> <<>>, p2 |-> <<>>]
        (* Process process1 *)
        /\ response = defaultInitValue
        (* Process process2 *)
        /\ buffer = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "SendToProcess2"
                                        [] self = 2 -> "ReceiveFromProcess1"]

SendToProcess2 == /\ pc[1] = "SendToProcess2"
                  /\ network' = [network EXCEPT ![p2] = Append(network[p2], "hello")]
                  /\ pc' = [pc EXCEPT ![1] = "ReceiveFromProcess2"]
                  /\ UNCHANGED << i, p1, p2, response, buffer >>

ReceiveFromProcess2 == /\ pc[1] = "ReceiveFromProcess2"
                       /\ Len(network[p2]) > 0
                       /\ response' = Head(network[p2])
                       /\ network' = [network EXCEPT ![p2] = Tail(@)]
                       /\ pc' = [pc EXCEPT ![1] = "Done"]
                       /\ UNCHANGED << i, p1, p2, buffer >>

process1 == SendToProcess2 \/ ReceiveFromProcess2

ReceiveFromProcess1 == /\ pc[2] = "ReceiveFromProcess1"
                       /\ Len(network[p1]) > 0
                       /\ buffer' = Head(network[p1])
                       /\ network' = [network EXCEPT ![p1] = Tail(@)]
                       /\ pc' = [pc EXCEPT ![2] = "SendToProcess1"]
                       /\ UNCHANGED << i, p1, p2, response >>

SendToProcess1 == /\ pc[2] = "SendToProcess1"
                  /\ network' = [network EXCEPT ![p1] = Append(network[p1], buffer)]
                  /\ pc' = [pc EXCEPT ![2] = "ReceiveFromProcess1"]
                  /\ UNCHANGED << i, p1, p2, response, buffer >>

process2 == ReceiveFromProcess1 \/ SendToProcess1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == process1 \/ process2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
