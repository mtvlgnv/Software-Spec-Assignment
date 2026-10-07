---------------------------- MODULE trash_single ----------------------------

EXTENDS trash_data


(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for trash bin
  outerDoorOpen = FALSE,
  outerDoorLocked = TRUE,
  trapDoorOpen = FALSE,
  ramExtended = FALSE,
  trashInTop = 0,
  trashCompressed = 0,
  trashUncompressed = 0,
  trashCapacity = MaxCapacity,
  trapDestroyed = FALSE,

  \* Variable for user
  userTrash = 0,

  \* Command for bin
  \* for command "change_outer_lock", open->TRUE means unlocked and open->FALSE means locked
  \* for command "change_ram", open->TRUE means ram extended and open->FALSE means ram retracted
  binCommand = [command |-> "finished", open |-> FALSE],
  \* Sensor from bin
  binSensor = [sensor |-> "idle"],
  \* Central scan requests of all users
  scans = << >>,
  \* Permissions per user
  permissions = << >>,
  \* Requests to/from server
  serverRequests = << >>,
  serverResponses = << >>,
  \* Command for the truck
  truckCommand = [command |-> "emptied", bin |-> 1];

define

\*****************************
\* Helper functions
\*****************************
\* You are free to add your own helper functions here.
Trash == trashCompressed + trashUncompressed
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity


\*****************************
\* Type checks
\*****************************
\* Check that variables use the correct type
TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1


\*****************************
\* Sanity checks (already given, feel free to use them)
\*****************************
CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded


\*****************************
\* Properties of interest
\*****************************
\* Replace FALSE by your own formalisation of each property.

\* The outer door can only be locked if it is closed.
OuterDoorLocked == FALSE
\* The vertical ram is only used when the outer door is closed and locked.
RamOuterDoor == FALSE
\* Every time the trash bin is full, it is eventually not full anymore.
TrashEmptied == FALSE
\* An unauthorized user cannot open the outer door.
AuthorizedOpenOnly == FALSE
\* The user infinitely often has trash and infinitely often has no trash.
UserTrash == FALSE
\* Every time the user has trash, they can deposit their trash.
UserTrashDeposited == FALSE
\* Every time the truck is requested for the trash bin, the truck has eventually emptied the bin.
TruckEmpties == FALSE

end define;


\*****************************
\* Helper macros
\*****************************

\* Compress trash
macro compress(compressed, uncompressed) begin
  compressed := compressed + IF (uncompressed > 1) THEN uncompressed \div 2 ELSE uncompressed;
  uncompressed := 0;
end macro

\* Read res from queue.
\* The macro awaits a non-empty queue.
macro read(queue, res) begin
  await queue /= <<>>;
  res := Head(queue);
  queue := Tail(queue);
end macro

\* Write msg to the queue.
macro write(queue, msg) begin
  queue := Append(queue, msg);
end macro


\*****************************
\* Process for a bin
\*****************************
process binProcess \in Bins
begin
  BinWaitForCommand:
    while TRUE do
      await binCommand.command /= "finished";
      if binCommand.command = "change_outer_door" then
        \* Open/Close outer door
        assert ~outerDoorLocked;
        outerDoorOpen := binCommand.open;
        if ~outerDoorOpen then
          binSensor := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand.command = "change_outer_lock" then
        \* Lock/Unlock outer door
        assert ~outerDoorOpen;
        outerDoorLocked := ~(binCommand.open);
      elsif binCommand.command = "change_trap_door" then
        assert outerDoorLocked;
        \* Open/Close trap door
        if ramExtended \/ CapacityExceeded then
            trapDestroyed := TRUE;
        end if;
        trapDoorOpen := binCommand.open;
        if trapDoorOpen then
          \* Trash falls through
          trashUncompressed := trashUncompressed + trashInTop;
          trashInTop := 0;
        end if
      elsif binCommand.command = "change_ram" then
        assert outerDoorLocked;
        \* Extend/Retract ram
        ramExtended := binCommand.open;
        if ramExtended then
          if ~trapDoorOpen then
            trapDestroyed := TRUE;
          end if;
          \* Compress trash
          compress(trashCompressed, trashUncompressed);
        end if;
      elsif binCommand.command = "empty" then
        \* Empty trash bin
        assert outerDoorLocked;
        assert ~trapDoorOpen;
        assert ~ramExtended;
        assert trashInTop = 0;
        assert trashUncompressed = 0;
        trashCompressed := 0;
      else
        \* should not happen
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand.command := "finished";
    end while;
end process;


\*****************************
\* Process for a user
\*****************************
process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE]
begin
  UserNextIteration:
    while TRUE do
      if userTrash = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash := amt;
        end with;
      end if;
  UserScanCard:
      write(scans, [user |-> self, bin |-> 1]);
  UserAwaitScanResponse:
      read(permissions, perm);
      assert perm.user = self;
      assert perm.bin = 1;
      if perm.granted then
  UserOpenDoor:
        binCommand := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand.command = "finished";
  UserDepositTrash:
        assert trashInTop = 0;
        trashInTop := userTrash;
        userTrash := 0;
  UserCloseDoor:
        binCommand := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand.command = "finished";
      end if;
    end while;
end process;


\*****************************
\* Process for a server
\*****************************
process serverProcess = Server
variables
  req = [user |-> 0]
begin
  ServerNextIteration:
    while TRUE do
  ServerAwaitRequest:
      read(serverRequests, req);
      with valid \in ValidCard(req.user) do
        write(serverResponses, [user |-> req.user, permission |-> valid]);
      end with;
    end while;
end process;


\*****************************
\* Process for a truck
\*****************************
\* Truck process.
\* Handshake with the controller via truckCommand:
\*   controller: "request" -> truck: "arrived" -> controller: "start_emptying"
\*   -> truck empties the bin -> truck: "emptied"
process truckProcess \in Trucks
begin
  TruckAwaitRequest:
    while TRUE do
      await truckCommand.command = "request";
  TruckArrive:
      \* Drive to the bin and report arrival
      truckCommand.command := "arrived";
  TruckAwaitStart:
      \* The controller hands over the (locked and idle) bin
      await truckCommand.command = "start_emptying";
      binCommand := [command |-> "empty", open |-> FALSE];
  TruckAwaitEmptied:
      await binCommand.command = "finished";
      truckCommand.command := "emptied";
    end while;
end process;


\*****************************
\* Process for the controller
\*****************************
\* Main control process.
\* The controller loops forever and in each iteration reacts to one event
\* that is ready, so it never blocks on a single thing:
\*   1. a new card scan                 -> check card and capacity, answer the user
\*   2. the user closed the outer door  -> process the deposit (lock, trap, ram)
\*   3. the requested truck arrived     -> hand the bin over to the truck
\*   4. the truck emptied the bin       -> accept deposits again
\* While a deposit is processed or the truck is busy, new scans are declined.
process controlProcess = Control
variables
  \* Scan currently being handled
  scan = [user |-> 0, bin |-> 0],
  \* Answer of the server for the current scan
  response = [user |-> 0, permission |-> FALSE],
  \* Phase of the bin:
  \*   "idle"       - door locked, trap closed, ram retracted; ready for a deposit
  \*   "depositing" - a user was granted access; deposit not processed yet
  \*   "truck"      - a truck was requested and has not emptied the bin yet
  binState = "idle"
begin
  ControlNextIteration:
    while TRUE do
      either
        \* 1. Handle a card scan
        read(scans, scan);
  ControlRequestServer:
        write(serverRequests, [user |-> scan.user]);
  ControlAwaitServer:
        read(serverResponses, response);
        if response.permission /\ binState = "idle" /\ TrashFitsCapacity(MaxUserTrash) then
  ControlUnlockDoor:
          \* The door must be unlocked before the user is allowed to open it
          await binCommand.command = "finished";
          binCommand := [command |-> "change_outer_lock", open |-> TRUE];
  ControlGrant:
          await binCommand.command = "finished";
          binState := "depositing";
          write(permissions, [user |-> scan.user, bin |-> scan.bin, granted |-> TRUE]);
        else
          \* Invalid card, bin busy or not enough capacity left
          write(permissions, [user |-> scan.user, bin |-> scan.bin, granted |-> FALSE]);
        end if;
      or
        \* 2. Process a deposit once the user closed the outer door.
        \* The bin sets the sensor before it marks the close command as finished,
        \* so also wait for "finished" before sending a new command.
        await /\ binState = "depositing"
              /\ binSensor.sensor = "outer_door_closed"
              /\ binCommand.command = "finished";
        binSensor := [sensor |-> "idle"];
        binCommand := [command |-> "change_outer_lock", open |-> FALSE];
  ControlOpenTrap:
        \* Trash falls from the outer door into the main compartment
        await binCommand.command = "finished";
        binCommand := [command |-> "change_trap_door", open |-> TRUE];
  ControlExtendRam:
        \* Compress only while the trap door is open
        await binCommand.command = "finished";
        binCommand := [command |-> "change_ram", open |-> TRUE];
  ControlRetractRam:
        await binCommand.command = "finished";
        binCommand := [command |-> "change_ram", open |-> FALSE];
  ControlCloseTrap:
        \* The ram is retracted, so the trap door can be closed safely
        await binCommand.command = "finished";
        binCommand := [command |-> "change_trap_door", open |-> FALSE];
  ControlFinishDeposit:
        await binCommand.command = "finished";
        if TrashFitsCapacity(MaxUserTrash) then
          binState := "idle";
        else
          \* The next deposit might not fit: request a truck
          binState := "truck";
          truckCommand := [command |-> "request", bin |-> 1];
        end if;
      or
        \* 3. The truck arrived: the bin is locked and idle, let the truck empty it
        await binState = "truck" /\ truckCommand.command = "arrived";
        truckCommand.command := "start_emptying";
      or
        \* 4. The truck emptied the bin: accept deposits again
        await binState = "truck" /\ truckCommand.command = "emptied";
        binState := "idle";
      end either;
    end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8de776c5" /\ chksum(tla) = "747f37d6")
VARIABLES outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, userTrash, binCommand, binSensor, scans, permissions, 
          serverRequests, serverResponses, truckCommand, pc

(* define statement *)
Trash == trashCompressed + trashUncompressed
CapacityExceeded == Trash > trashCapacity
TrashFitsCapacity(trash) == Trash + trash <= trashCapacity






TypeOK == /\ outerDoorOpen \in BOOLEAN
          /\ outerDoorLocked \in BOOLEAN
          /\ trapDoorOpen \in BOOLEAN
          /\ ramExtended \in BOOLEAN
          /\ trashInTop \in Nat
          /\ trashCompressed \in Nat
          /\ trashUncompressed \in Nat
          /\ trashCapacity \in Nat
          /\ trapDestroyed \in BOOLEAN
          /\ binCommand.command \in BinCommand
          /\ binCommand.open \in BOOLEAN
          /\ binSensor.sensor \in BinSensor
          /\ userTrash \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A i \in 1..Len(permissions):
               /\ permissions[i].user \in Users
               /\ permissions[i].bin \in Bins
               /\ permissions[i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ truckCommand.command \in TruckCommand
          /\ truckCommand.bin \in Bins


MessagesOK == /\ Len(scans) <= 1
              /\ Len(permissions) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1





CapacitiesRespected == /\ trashUncompressed >= 0
                       /\ trashUncompressed <= trashCapacity
                       /\ trashCompressed >= 0
                       /\ trashCompressed <= trashCapacity
                       /\ trashCapacity >= 0
                       /\ trashCapacity <= MaxCapacity
TrapNotDestroyed == ~trapDestroyed
CapacityNotExceeded == ~CapacityExceeded








OuterDoorLocked == FALSE

RamOuterDoor == FALSE

TrashEmptied == FALSE

AuthorizedOpenOnly == FALSE

UserTrash == FALSE

UserTrashDeposited == FALSE

TruckEmpties == FALSE

VARIABLES perm, req, scan, response, binState

vars == << outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, userTrash, binCommand, binSensor, scans, 
           permissions, serverRequests, serverResponses, truckCommand, pc, 
           perm, req, scan, response, binState >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = FALSE
        /\ outerDoorLocked = TRUE
        /\ trapDoorOpen = FALSE
        /\ ramExtended = FALSE
        /\ trashInTop = 0
        /\ trashCompressed = 0
        /\ trashUncompressed = 0
        /\ trashCapacity = MaxCapacity
        /\ trapDestroyed = FALSE
        /\ userTrash = 0
        /\ binCommand = [command |-> "finished", open |-> FALSE]
        /\ binSensor = [sensor |-> "idle"]
        /\ scans = << >>
        /\ permissions = << >>
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [command |-> "emptied", bin |-> 1]
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        (* Process serverProcess *)
        /\ req = [user |-> 0]
        (* Process controlProcess *)
        /\ scan = [user |-> 0, bin |-> 0]
        /\ response = [user |-> 0, permission |-> FALSE]
        /\ binState = "idle"
        /\ pc = [self \in ProcSet |-> CASE self \in Bins -> "BinWaitForCommand"
                                        [] self \in Users -> "UserNextIteration"
                                        [] self = Server -> "ServerNextIteration"
                                        [] self \in Trucks -> "TruckAwaitRequest"
                                        [] self = Control -> "ControlNextIteration"]

BinWaitForCommand(self) == /\ pc[self] = "BinWaitForCommand"
                           /\ binCommand.command /= "finished"
                           /\ IF binCommand.command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked, 
                                                "Failure of assertion at line 162, column 9.")
                                      /\ outerDoorOpen' = binCommand.open
                                      /\ IF ~outerDoorOpen'
                                            THEN /\ binSensor' = [sensor |-> "outer_door_closed"]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand.command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen, 
                                                           "Failure of assertion at line 169, column 9.")
                                                 /\ outerDoorLocked' = ~(binCommand.open)
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand.command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked, 
                                                                      "Failure of assertion at line 172, column 9.")
                                                            /\ IF ramExtended \/ CapacityExceeded
                                                                  THEN /\ trapDestroyed' = TRUE
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = binCommand.open
                                                            /\ IF trapDoorOpen'
                                                                  THEN /\ trashUncompressed' = trashUncompressed + trashInTop
                                                                       /\ trashInTop' = 0
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand.command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked, 
                                                                                 "Failure of assertion at line 184, column 9.")
                                                                       /\ ramExtended' = binCommand.open
                                                                       /\ IF ramExtended'
                                                                             THEN /\ IF ~trapDoorOpen
                                                                                        THEN /\ trapDestroyed' = TRUE
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = (trashCompressed + IF (trashUncompressed > 1) THEN trashUncompressed \div 2 ELSE trashUncompressed)
                                                                                  /\ trashUncompressed' = 0
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand.command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked, 
                                                                                            "Failure of assertion at line 196, column 9.")
                                                                                  /\ Assert(~trapDoorOpen, 
                                                                                            "Failure of assertion at line 197, column 9.")
                                                                                  /\ Assert(~ramExtended, 
                                                                                            "Failure of assertion at line 198, column 9.")
                                                                                  /\ Assert(trashInTop = 0, 
                                                                                            "Failure of assertion at line 199, column 9.")
                                                                                  /\ Assert(trashUncompressed = 0, 
                                                                                            "Failure of assertion at line 200, column 9.")
                                                                                  /\ trashCompressed' = 0
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 204, column 9.")
                                                                                  /\ UNCHANGED trashCompressed
                                                                       /\ UNCHANGED << ramExtended, 
                                                                                       trashUncompressed, 
                                                                                       trapDestroyed >>
                                                            /\ UNCHANGED << trapDoorOpen, 
                                                                            trashInTop >>
                                                 /\ UNCHANGED outerDoorLocked
                                      /\ UNCHANGED << outerDoorOpen, binSensor >>
                           /\ pc' = [pc EXCEPT ![self] = "BinCommandFinished"]
                           /\ UNCHANGED << trashCapacity, userTrash, 
                                           binCommand, scans, permissions, 
                                           serverRequests, serverResponses, 
                                           truckCommand, perm, req, scan, 
                                           response, binState >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT !.command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            binSensor, scans, permissions, 
                                            serverRequests, serverResponses, 
                                            truckCommand, perm, req, scan, 
                                            response, binState >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "UserNewTrash"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           req, scan, response, binState >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ scans' = Append(scans, ([user |-> self, bin |-> 1]))
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, perm, req, scan, response, 
                                      binState >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ permissions /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head(permissions)]
                               /\ permissions' = Tail(permissions)
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 231, column 7.")
                               /\ Assert(perm'[self].bin = 1, 
                                         "Failure of assertion at line 232, column 7.")
                               /\ IF perm'[self].granted
                                     THEN /\ pc' = [pc EXCEPT ![self] = "UserOpenDoor"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                               trapDoorOpen, ramExtended, 
                                               trashInTop, trashCompressed, 
                                               trashUncompressed, 
                                               trashCapacity, trapDestroyed, 
                                               userTrash, binCommand, 
                                               binSensor, scans, 
                                               serverRequests, serverResponses, 
                                               truckCommand, req, scan, 
                                               response, binState >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [command |-> "change_outer_door", open |-> TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, perm, req, scan, response, 
                                      binState >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand.command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           req, scan, response, binState >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop = 0, 
                                    "Failure of assertion at line 239, column 9.")
                          /\ trashInTop' = userTrash
                          /\ userTrash' = 0
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          binCommand, binSensor, scans, 
                                          permissions, serverRequests, 
                                          serverResponses, truckCommand, perm, 
                                          req, scan, response, binState >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [command |-> "change_outer_door", open |-> FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, perm, req, scan, response, 
                                       binState >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand.command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userTrash, 
                                             binCommand, binSensor, scans, 
                                             permissions, serverRequests, 
                                             serverResponses, truckCommand, 
                                             perm, req, scan, response, 
                                             binState >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = amt
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, perm, req, scan, response, 
                                      binState >>

userProcess(self) == UserNextIteration(self) \/ UserScanCard(self)
                        \/ UserAwaitScanResponse(self)
                        \/ UserOpenDoor(self) \/ UserAwaitOpenDoor(self)
                        \/ UserDepositTrash(self) \/ UserCloseDoor(self)
                        \/ UserAwaitClosedDoor(self) \/ UserNewTrash(self)

ServerNextIteration == /\ pc[Server] = "ServerNextIteration"
                       /\ pc' = [pc EXCEPT ![Server] = "ServerAwaitRequest"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binCommand, binSensor, scans, 
                                       permissions, serverRequests, 
                                       serverResponses, truckCommand, perm, 
                                       req, scan, response, binState >>

ServerAwaitRequest == /\ pc[Server] = "ServerAwaitRequest"
                      /\ serverRequests /= <<>>
                      /\ req' = Head(serverRequests)
                      /\ serverRequests' = Tail(serverRequests)
                      /\ \E valid \in ValidCard(req'.user):
                           serverResponses' = Append(serverResponses, ([user |-> req'.user, permission |-> valid]))
                      /\ pc' = [pc EXCEPT ![Server] = "ServerNextIteration"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      permissions, truckCommand, perm, scan, 
                                      response, binState >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckAwaitRequest(self) == /\ pc[self] = "TruckAwaitRequest"
                           /\ truckCommand.command = "request"
                           /\ pc' = [pc EXCEPT ![self] = "TruckArrive"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, perm, 
                                           req, scan, response, binState >>

TruckArrive(self) == /\ pc[self] = "TruckArrive"
                     /\ truckCommand' = [truckCommand EXCEPT !.command = "arrived"]
                     /\ pc' = [pc EXCEPT ![self] = "TruckAwaitStart"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binCommand, binSensor, scans, permissions, 
                                     serverRequests, serverResponses, perm, 
                                     req, scan, response, binState >>

TruckAwaitStart(self) == /\ pc[self] = "TruckAwaitStart"
                         /\ truckCommand.command = "start_emptying"
                         /\ binCommand' = [command |-> "empty", open |-> FALSE]
                         /\ pc' = [pc EXCEPT ![self] = "TruckAwaitEmptied"]
                         /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                         trapDoorOpen, ramExtended, trashInTop, 
                                         trashCompressed, trashUncompressed, 
                                         trashCapacity, trapDestroyed, 
                                         userTrash, binSensor, scans, 
                                         permissions, serverRequests, 
                                         serverResponses, truckCommand, perm, 
                                         req, scan, response, binState >>

TruckAwaitEmptied(self) == /\ pc[self] = "TruckAwaitEmptied"
                           /\ binCommand.command = "finished"
                           /\ truckCommand' = [truckCommand EXCEPT !.command = "emptied"]
                           /\ pc' = [pc EXCEPT ![self] = "TruckAwaitRequest"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, perm, req, scan, 
                                           response, binState >>

truckProcess(self) == TruckAwaitRequest(self) \/ TruckArrive(self)
                         \/ TruckAwaitStart(self)
                         \/ TruckAwaitEmptied(self)

ControlNextIteration == /\ pc[Control] = "ControlNextIteration"
                        /\ \/ /\ scans /= <<>>
                              /\ scan' = Head(scans)
                              /\ scans' = Tail(scans)
                              /\ pc' = [pc EXCEPT ![Control] = "ControlRequestServer"]
                              /\ UNCHANGED <<binCommand, binSensor, truckCommand, binState>>
                           \/ /\ /\ binState = "depositing"
                                 /\ binSensor.sensor = "outer_door_closed"
                                 /\ binCommand.command = "finished"
                              /\ binSensor' = [sensor |-> "idle"]
                              /\ binCommand' = [command |-> "change_outer_lock", open |-> FALSE]
                              /\ pc' = [pc EXCEPT ![Control] = "ControlOpenTrap"]
                              /\ UNCHANGED <<scans, truckCommand, scan, binState>>
                           \/ /\ binState = "truck" /\ truckCommand.command = "arrived"
                              /\ truckCommand' = [truckCommand EXCEPT !.command = "start_emptying"]
                              /\ pc' = [pc EXCEPT ![Control] = "ControlNextIteration"]
                              /\ UNCHANGED <<binCommand, binSensor, scans, scan, binState>>
                           \/ /\ binState = "truck" /\ truckCommand.command = "emptied"
                              /\ binState' = "idle"
                              /\ pc' = [pc EXCEPT ![Control] = "ControlNextIteration"]
                              /\ UNCHANGED <<binCommand, binSensor, scans, truckCommand, scan>>
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, permissions, serverRequests, 
                                        serverResponses, perm, req, response >>

ControlRequestServer == /\ pc[Control] = "ControlRequestServer"
                        /\ serverRequests' = Append(serverRequests, ([user |-> scan.user]))
                        /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitServer"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, binCommand, binSensor, 
                                        scans, permissions, serverResponses, 
                                        truckCommand, perm, req, scan, 
                                        response, binState >>

ControlAwaitServer == /\ pc[Control] = "ControlAwaitServer"
                      /\ serverResponses /= <<>>
                      /\ response' = Head(serverResponses)
                      /\ serverResponses' = Tail(serverResponses)
                      /\ IF response'.permission /\ binState = "idle" /\ TrashFitsCapacity(MaxUserTrash)
                            THEN /\ pc' = [pc EXCEPT ![Control] = "ControlUnlockDoor"]
                                 /\ UNCHANGED permissions
                            ELSE /\ permissions' = Append(permissions, ([user |-> scan.user, bin |-> scan.bin, granted |-> FALSE]))
                                 /\ pc' = [pc EXCEPT ![Control] = "ControlNextIteration"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      serverRequests, truckCommand, perm, req, 
                                      scan, binState >>

ControlUnlockDoor == /\ pc[Control] = "ControlUnlockDoor"
                     /\ binCommand.command = "finished"
                     /\ binCommand' = [command |-> "change_outer_lock", open |-> TRUE]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlGrant"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, perm, req, scan, response, 
                                     binState >>

ControlGrant == /\ pc[Control] = "ControlGrant"
                /\ binCommand.command = "finished"
                /\ binState' = "depositing"
                /\ permissions' = Append(permissions, ([user |-> scan.user, bin |-> scan.bin, granted |-> TRUE]))
                /\ pc' = [pc EXCEPT ![Control] = "ControlNextIteration"]
                /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                                ramExtended, trashInTop, trashCompressed, 
                                trashUncompressed, trashCapacity, 
                                trapDestroyed, userTrash, binCommand, 
                                binSensor, scans, serverRequests, 
                                serverResponses, truckCommand, perm, req, scan, 
                                response >>

ControlOpenTrap == /\ pc[Control] = "ControlOpenTrap"
                   /\ binCommand.command = "finished"
                   /\ binCommand' = [command |-> "change_trap_door", open |-> TRUE]
                   /\ pc' = [pc EXCEPT ![Control] = "ControlExtendRam"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, userTrash, 
                                   binSensor, scans, permissions, 
                                   serverRequests, serverResponses, 
                                   truckCommand, perm, req, scan, response, 
                                   binState >>

ControlExtendRam == /\ pc[Control] = "ControlExtendRam"
                    /\ binCommand.command = "finished"
                    /\ binCommand' = [command |-> "change_ram", open |-> TRUE]
                    /\ pc' = [pc EXCEPT ![Control] = "ControlRetractRam"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, req, scan, response, 
                                    binState >>

ControlRetractRam == /\ pc[Control] = "ControlRetractRam"
                     /\ binCommand.command = "finished"
                     /\ binCommand' = [command |-> "change_ram", open |-> FALSE]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlCloseTrap"]
                     /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                     trapDoorOpen, ramExtended, trashInTop, 
                                     trashCompressed, trashUncompressed, 
                                     trashCapacity, trapDestroyed, userTrash, 
                                     binSensor, scans, permissions, 
                                     serverRequests, serverResponses, 
                                     truckCommand, perm, req, scan, response, 
                                     binState >>

ControlCloseTrap == /\ pc[Control] = "ControlCloseTrap"
                    /\ binCommand.command = "finished"
                    /\ binCommand' = [command |-> "change_trap_door", open |-> FALSE]
                    /\ pc' = [pc EXCEPT ![Control] = "ControlFinishDeposit"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, perm, req, scan, response, 
                                    binState >>

ControlFinishDeposit == /\ pc[Control] = "ControlFinishDeposit"
                        /\ binCommand.command = "finished"
                        /\ IF TrashFitsCapacity(MaxUserTrash)
                              THEN /\ binState' = "idle"
                                   /\ UNCHANGED truckCommand
                              ELSE /\ binState' = "truck"
                                   /\ truckCommand' = [command |-> "request", bin |-> 1]
                        /\ pc' = [pc EXCEPT ![Control] = "ControlNextIteration"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, binCommand, binSensor, 
                                        scans, permissions, serverRequests, 
                                        serverResponses, perm, req, scan, 
                                        response >>

controlProcess == ControlNextIteration \/ ControlRequestServer
                     \/ ControlAwaitServer \/ ControlUnlockDoor
                     \/ ControlGrant \/ ControlOpenTrap \/ ControlExtendRam
                     \/ ControlRetractRam \/ ControlCloseTrap
                     \/ ControlFinishDeposit

Next == serverProcess \/ controlProcess
           \/ (\E self \in Bins: binProcess(self))
           \/ (\E self \in Users: userProcess(self))
           \/ (\E self \in Trucks: truckProcess(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


=============================================================================
\* Modification History
