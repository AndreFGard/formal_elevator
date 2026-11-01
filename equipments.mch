MACHINE
      equipments
SETS
    DoorState = {kOpen, kClosed};
    Direction = {kUp, kDown, kStopped}
CONSTANTS
    kNLevels, kMaxDoorOpenTime, kMaxWeight
PROPERTIES
    kNLevels : NAT &
    kNLevels = 5 &
    kMaxDoorOpenTime : NAT &
    kMaxDoorOpenTime = 5 &
    kMaxWeight : NAT &
    kMaxWeight = 150 
VARIABLES
    level,
    direction,
    door,
    door_open_time,
    weight,
    is_maintenance
INVARIANT
    level : 1..(kNLevels+1) &
    direction : Direction &
    door : DoorState &
    door_open_time : NAT &
    weight : NAT &
    is_maintenance : BOOL &
    
    (is_maintenance = TRUE => direction = kStopped) &
    (direction /= kStopped => door = kClosed) &
    (weight > kMaxWeight => direction = kStopped) &
    
    (door_open_time > 0 => door = kOpen)
INITIALISATION
    level := 1 ||
    direction := kStopped ||
    door := kClosed ||
    door_open_time := 0 ||
    weight := 0 ||
    is_maintenance := FALSE
OPERATIONS
    Move(new_direction) =
    PRE
        weight <= kMaxWeight &
        new_direction : Direction &
        (new_direction = direction or direction = kStopped) &
        door = kClosed &
        is_maintenance = FALSE &
        (new_direction = kUp or new_direction = kDown) &
        (new_direction = kUp => level /= (kNLevels + 1)) &
        (new_direction = kDown => level /= 1)
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
    
    CloseDoor = BEGIN
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
        weighs:NAT
    THEN
        weight := weight + weighs
    END;
    
    //MAINTENANCE
    EnableMaintenance = 
    PRE
        direction = kStopped 
    THEN
        is_maintenance := TRUE
    END;
     
     DisableMaintenance = 
     PRE 
        is_maintenance = TRUE &
        direction = kStopped
     THEN 
         is_maintenance := FALSE
     END
 
END