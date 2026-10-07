----------------------------- MODULE trash_data -----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

\*****************************
\* Define constants
\*****************************
CONSTANTS
  NumBins,
  NumUsers,
  NumTrucks,
  MaxCapacity,
  MaxUserTrash
ASSUME NumBins \in Nat /\ NumBins >= 1
  /\ NumUsers \in Nat /\ NumUsers >= 1
  /\ NumTrucks \in Nat /\ NumTrucks >= 1
  /\ MaxCapacity \in Nat /\ MaxCapacity >= 1
  /\ MaxUserTrash \in Nat /\ MaxUserTrash >= 1 /\ MaxUserTrash <= MaxCapacity


\*****************************
\* Define data structures
\*****************************

\* Control process is first
Control == 0
\* Bins
Bins == 1..NumBins
\* Users have higher ids than trash bins
\* This is needed to avoid overlap with the bin process ids
Users == (NumBins+1)..(NumBins+NumUsers)
\* Trucks start after Users
Trucks == (NumBins+NumUsers+1)..(NumBins+NumUsers+NumTrucks)
\* Server is last
Server == NumBins+NumUsers+NumTrucks+1

\* Data types
\* Commands for trucks
TruckCommand == {"request", "arrived", "start_emptying", "emptied"}
\* Commands for trash bin
BinCommand == {"change_outer_door", "change_outer_lock", "change_trap_door", "change_ram", "empty", "finished"}
\* Commands from outer door sensor
BinSensor == {"outer_door_closed", "idle"}

\*****************************
\* Helper functions
\*****************************
UserOffset == NumBins+1
TruckOffset == UserOffset+NumUsers

\* Possible validity results for a user's card
ValidCard(user) == {user # 42}

=============================================================================
\* Modification History
