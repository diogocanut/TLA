-------------------------- MODULE echo --------------------------

EXTENDS Integers, Sequences, TLC
(* --algorithm echo

variables
  i = 0;
  network = [A |-> <<>>, B |-> <<>>];

macro send(to, msg) begin
  network[to] := Append(network[to], msg);
end macro;

macro receive(p, buffer) begin
  await Len(network[p]) > 0;
  buffer := Head(network[p]);
  network[p] := Tail(@);
end macro;

process processA = "A"
variable response;
begin
  Iterate:
    while i < 10 do
      SendToProcessB:
        send("B", "Hello");
      ReceiveFromProcessB:
        receive("A", response);
      i := i + 1;
    end while;
end process;

process processB = "B"
variable buffer;
begin
  ReceiveFromProcessA:
    receive("B", buffer);
    SendToProcessA:
      send("A", buffer);
  if i < 9 then
    goto ReceiveFromProcessA;
  end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "5a83a861" /\ chksum(tla) = "5a540906")
CONSTANT defaultInitValue
VARIABLES pc, i, network, response, buffer

vars == << pc, i, network, response, buffer >>

ProcSet == {"A"} \cup {"B"}

Init == (* Global variables *)
        /\ i = 0
        /\ network = [A |-> <<>>, B |-> <<>>]
        (* Process processA *)
        /\ response = defaultInitValue
        (* Process processB *)
        /\ buffer = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "A" -> "Iterate"
                                        [] self = "B" -> "ReceiveFromProcessA"]

Iterate == /\ pc["A"] = "Iterate"
           /\ IF i < 10
                 THEN /\ pc' = [pc EXCEPT !["A"] = "SendToProcessB"]
                 ELSE /\ pc' = [pc EXCEPT !["A"] = "Done"]
           /\ UNCHANGED << i, network, response, buffer >>

SendToProcessB == /\ pc["A"] = "SendToProcessB"
                  /\ network' = [network EXCEPT !["B"] = Append(network["B"], "Hello")]
                  /\ pc' = [pc EXCEPT !["A"] = "ReceiveFromProcessB"]
                  /\ UNCHANGED << i, response, buffer >>

ReceiveFromProcessB == /\ pc["A"] = "ReceiveFromProcessB"
                       /\ Len(network["A"]) > 0
                       /\ response' = Head(network["A"])
                       /\ network' = [network EXCEPT !["A"] = Tail(@)]
                       /\ i' = i + 1
                       /\ pc' = [pc EXCEPT !["A"] = "Iterate"]
                       /\ UNCHANGED buffer

processA == Iterate \/ SendToProcessB \/ ReceiveFromProcessB

ReceiveFromProcessA == /\ pc["B"] = "ReceiveFromProcessA"
                       /\ Len(network["B"]) > 0
                       /\ buffer' = Head(network["B"])
                       /\ network' = [network EXCEPT !["B"] = Tail(@)]
                       /\ pc' = [pc EXCEPT !["B"] = "SendToProcessA"]
                       /\ UNCHANGED << i, response >>

SendToProcessA == /\ pc["B"] = "SendToProcessA"
                  /\ network' = [network EXCEPT !["A"] = Append(network["A"], buffer)]
                  /\ IF i < 9
                        THEN /\ pc' = [pc EXCEPT !["B"] = "ReceiveFromProcessA"]
                        ELSE /\ pc' = [pc EXCEPT !["B"] = "Done"]
                  /\ UNCHANGED << i, response, buffer >>

processB == ReceiveFromProcessA \/ SendToProcessA

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == processA \/ processB
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
