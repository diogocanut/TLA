-------------------------- MODULE echo --------------------------

EXTENDS Integers, Sequences, TLC, Channels


(* --algorithm echo
variables
  i = 0;
  channel = Channels({"A", "B"});

macro send(to, msg) begin
  channel := SendToChannel(channel, to, msg);
end macro;

macro receive(p, buffer) begin
  await HasMessage(channel, p);
  buffer := NextMessage(channel, p);
  channel := MarkMessageReceived(channel, p);
end macro;

process processA = "A"
variable response;
begin
  Iterate:
    while i < 10 do
      Send:
        send("B", "Hello");
      Receive:
        receive("A", response);
      i := i + 1;
    end while;
end process;

process processB = "B"
variable buffer;
begin
  Receive:
    receive("B", buffer);
  Send:
    send("A", buffer);
  if i < 9 then
    goto ReceiveFromProcessA;
  end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "1c0e03e1" /\ chksum(tla) = "490673a6")
CONSTANT defaultInitValue
VARIABLES pc, i, channel, response, buffer

vars == << pc, i, channel, response, buffer >>

ProcSet == {"A"} \cup {"B"}

Init == (* Global variables *)
        /\ i = 0
        /\ channel = Channels({"A", "B"})
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
           /\ UNCHANGED << i, channel, response, buffer >>

SendToProcessB == /\ pc["A"] = "SendToProcessB"
                  /\ channel' = SendToChannel(channel, "B", "Hello")
                  /\ pc' = [pc EXCEPT !["A"] = "ReceiveFromProcessB"]
                  /\ UNCHANGED << i, response, buffer >>

ReceiveFromProcessB == /\ pc["A"] = "ReceiveFromProcessB"
                       /\ HasMessage(channel, "A")
                       /\ response' = NextMessage(channel, "A")
                       /\ channel' = MarkMessageReceived(channel, "A")
                       /\ i' = i + 1
                       /\ pc' = [pc EXCEPT !["A"] = "Iterate"]
                       /\ UNCHANGED buffer

processA == Iterate \/ SendToProcessB \/ ReceiveFromProcessB

ReceiveFromProcessA == /\ pc["B"] = "ReceiveFromProcessA"
                       /\ HasMessage(channel, "B")
                       /\ buffer' = NextMessage(channel, "B")
                       /\ channel' = MarkMessageReceived(channel, "B")
                       /\ pc' = [pc EXCEPT !["B"] = "SendToProcessA"]
                       /\ UNCHANGED << i, response >>

SendToProcessA == /\ pc["B"] = "SendToProcessA"
                  /\ channel' = SendToChannel(channel, "A", buffer)
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
