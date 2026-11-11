MACHINE
      equipments
SETS
    DoorState = {kOpen, kClosed};
    Direction = {kUp, kDown, kStopped};
    LedState = {ON, OFF, BLINK}
CONSTANTS
    kNLevels, kMaxDoorOpenTime, kMaxWeight
PROPERTIES
    kNLevels : NATURAL &
    kNLevels = 5 &
    kMaxDoorOpenTime : NATURAL &
    // Represetns 120s
    kMaxDoorOpenTime = 4 &
    kMaxWeight : NATURAL &
    // Represents 450  
    kMaxWeight = 5 
VARIABLES
    level,
    direction,
    door,
    door_open_time,
    door_blocked,
    weight,
    is_maintenance,
    maintenance_requested
INVARIANT
    level : 1..(kNLevels) &
    direction : Direction &
    door : DoorState &
    door_blocked: BOOL &
    door_open_time : NATURAL &
    weight : NATURAL &
    is_maintenance : BOOL &
    maintenance_requested: BOOL  &
    
    (is_maintenance = TRUE => direction = kStopped & door = kOpen) &
    (direction /= kStopped => door = kClosed) &
    (weight > kMaxWeight => (direction = kStopped & door =kOpen)) &
    (door_open_time > 0 => door = kOpen) &
    (door_blocked = TRUE => door = kOpen)
INITIALISATION
    level := 1 ||
    direction := kStopped ||
    door := kClosed ||
    door_blocked := FALSE ||
    door_open_time := 0 ||
    weight := 0 ||
    is_maintenance := FALSE ||
    maintenance_requested := FALSE
DEFINITIONS
    CAN_MOVE(dir) == (
        weight <= kMaxWeight &
        dir : Direction &
        (dir = direction or direction = kStopped) &
        door = kClosed &
        is_maintenance = FALSE &
        (dir = kUp or dir = kDown) &
        (dir = kUp => level /= kNLevels) &
        (dir = kDown => level /= 1))
OPERATIONS
    Move(new_direction) =
    PRE
        new_direction: Direction &
        CAN_MOVE(new_direction)
    THEN
        IF new_direction = kUp THEN
            level := level + 1 ||
            direction := new_direction
        ELSE
            level := level - 1 ||
            direction := new_direction
        END
    END;
    // DOOR
    Stop = BEGIN
        direction := kStopped
    END;
    
    OpenDoor =
    PRE
        direction = kStopped
    THEN
        door:= kOpen
    END;
    
    CloseDoor = PRE
        weight <= kMaxWeight &
        is_maintenance = FALSE &
        door_blocked = FALSE
    THEN
        door, door_open_time := kClosed, 0
     END;
    // Updates anything regarding timers.
    TickDoor = BEGIN
        IF door = kOpen THEN door_open_time   := min({door_open_time +1,kMaxDoorOpenTime}) END
    END;
    
    // WEIGHT
    AddPassenger(weighs) = 
    PRE
        direction = kStopped & 
        door = kOpen &
        weighs:NAT
    THEN
        weight := weight + weighs
    END;
    
    RemovePassenger(weighs) = 
    PRE
        direction = kStopped & 
        door = kOpen &
        weighs:NAT &
        weighs <= weight
    THEN
        weight := weight - weighs
    END;
    
    
    BlockDoor = 
    PRE
        door = kOpen
    THEN
        door_blocked := TRUE
    END;
    
    UnblockDoor = 
    PRE
        door = kOpen &
        door_blocked = TRUE
    THEN
        door_blocked := FALSE
    END;
        
    //MAINTENANCE
    EnableMaintenance = 
    PRE
        direction = kStopped  &
        door = kOpen
    THEN
        is_maintenance := TRUE
    END;
     
     DisableMaintenance = 
     PRE 
        is_maintenance = TRUE &
        direction = kStopped
     THEN 
         is_maintenance := FALSE
     END;
    
    ToggleMaintenanceKey = BEGIN
        maintenance_requested := bool(maintenance_requested = FALSE)
    END
 
END