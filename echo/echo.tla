-------------------------- MODULE echo --------------------------

EXTENDS Integers, Sequences, TLC
(* --algorithm echo

variables
  i = 0;
  p1 = "p1";
  p2 = "p2";
  network = [p1 |-> <<>>, p2 |-> <<>>];
  isNetworkHealthy = TRUE;

define
  MessageEchoed == 
  /\ Len(network[p1]) <= 1
  /\ Len(network[p2]) <= 1

  SendReceiveResponse == 
  [](Len(network[p2]) > 0 => <> (Len(network[p1]) > 0))

  NetworkEventuallyBecomesHealthy ==
  []<>(isNetworkHealthy)
end define;

macro send(to, msg) begin
  
  \* either
  \*   isNetworkHealthy := TRUE;
  \* or
  \*   isNetworkHealthy := FALSE;
  \* end either;

  if isNetworkHealthy then
    network[to] := Append(network[to], msg);
  end if;
end macro;

macro receive(p, buffer) begin
  await Len(network[p]) > 0;
  buffer := Head(network[p]);
  network[p] := Tail(@);
end macro;

process process1 = 1
variable response;
begin
  Iterate:
    while i < 10 do
      SendToProcess2:
        send(p2, i);
      ReceiveFromProcess2:
        receive(p1, response);
      i := i + 1;
    end while;
end process;

process process2 = 2
variable buffer;
begin
  ReceiveFromProcess1:
    receive(p2, buffer);
    SendToProcess1:
      send(p1, buffer);
    goto ReceiveFromProcess1;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "520f43c3" /\ chksum(tla) = "fb45479f")
CONSTANT defaultInitValue
VARIABLES pc, i, p1, p2, network, isNetworkHealthy

(* define statement *)
MessageEchoed ==
/\ Len(network[p1]) <= 1
/\ Len(network[p2]) <= 1

SendReceiveResponse ==
[](Len(network[p2]) > 0 => <> (Len(network[p1]) > 0))

NetworkEventuallyBecomesHealthy ==
[]<>(isNetworkHealthy)

VARIABLES response, buffer

vars == << pc, i, p1, p2, network, isNetworkHealthy, response, buffer >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ i = 0
        /\ p1 = "p1"
        /\ p2 = "p2"
        /\ network = [p1 |-> <<>>, p2 |-> <<>>]
        /\ isNetworkHealthy = TRUE
        (* Process process1 *)
        /\ response = defaultInitValue
        (* Process process2 *)
        /\ buffer = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "Iterate"
                                        [] self = 2 -> "ReceiveFromProcess1"]

Iterate == /\ pc[1] = "Iterate"
           /\ IF i < 10
                 THEN /\ pc' = [pc EXCEPT ![1] = "SendToProcess2"]
                 ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
           /\ UNCHANGED << i, p1, p2, network, isNetworkHealthy, response, 
                           buffer >>

SendToProcess2 == /\ pc[1] = "SendToProcess2"
                  /\ IF isNetworkHealthy
                        THEN /\ network' = [network EXCEPT ![p2] = Append(network[p2], i)]
                        ELSE /\ TRUE
                             /\ UNCHANGED network
                  /\ pc' = [pc EXCEPT ![1] = "ReceiveFromProcess2"]
                  /\ UNCHANGED << i, p1, p2, isNetworkHealthy, response, 
                                  buffer >>

ReceiveFromProcess2 == /\ pc[1] = "ReceiveFromProcess2"
                       /\ Len(network[p1]) > 0
                       /\ response' = Head(network[p1])
                       /\ network' = [network EXCEPT ![p1] = Tail(@)]
                       /\ i' = i + 1
                       /\ pc' = [pc EXCEPT ![1] = "Iterate"]
                       /\ UNCHANGED << p1, p2, isNetworkHealthy, buffer >>

process1 == Iterate \/ SendToProcess2 \/ ReceiveFromProcess2

ReceiveFromProcess1 == /\ pc[2] = "ReceiveFromProcess1"
                       /\ Len(network[p2]) > 0
                       /\ buffer' = Head(network[p2])
                       /\ network' = [network EXCEPT ![p2] = Tail(@)]
                       /\ pc' = [pc EXCEPT ![2] = "SendToProcess1"]
                       /\ UNCHANGED << i, p1, p2, isNetworkHealthy, response >>

SendToProcess1 == /\ pc[2] = "SendToProcess1"
                  /\ IF isNetworkHealthy
                        THEN /\ network' = [network EXCEPT ![p1] = Append(network[p1], buffer)]
                        ELSE /\ TRUE
                             /\ UNCHANGED network
                  /\ pc' = [pc EXCEPT ![2] = "ReceiveFromProcess1"]
                  /\ UNCHANGED << i, p1, p2, isNetworkHealthy, response, 
                                  buffer >>

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
