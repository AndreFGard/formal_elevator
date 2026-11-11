MACHINE
    controller
EXTENDS equipments, buttons
/*
PROMOTES
      press_level, press_up, press_down,
      BlockDoor,ToggleMaintenanceKey,RemovePassenger,AddPassenger,
      release_level, release_up, release_down, tick_buttons
*/
SETS
    MainState = {kNoObjective, kMaintenance, kWorking,kClosing,kOpening,kWaitingBoarding}
VARIABLES
    broader_direction,    
    state,
    objective
INVARIANT
    broader_direction : Direction &
    state: MainState &
    objective : 1..kNLevels &
    
    //Some can be moved to main to save POs
    (state = kNoObjective => direction = kStopped) &
    (broader_direction = kStopped => state /= kWorking) &
    (is_maintenance = TRUE => state = kMaintenance) &
    (state = kOpening => is_maintenance = FALSE) &
    (state = kWorking => door = kClosed & broader_direction /= kStopped)
    
INITIALISATION
    broader_direction := kStopped ||
    state := kNoObjective ||
    objective := 1 
DEFINITIONS
CAN_MOVE_CONT(new_dir) == (
    new_dir: Direction & 
    weight <= kMaxWeight &
    n_passengers <= kMaxPassengers &
    (new_dir = direction or direction = kStopped) &
    door = kClosed &
    is_maintenance = FALSE &
    (new_dir = kUp or new_dir = kDown) &
    (new_dir = kUp => level /= kNLevels) &
    (new_dir = kDown => level /= 1)
);

ALL_OBJECTIVES == (requests \/ up_requests \/ down_requests);

//TODO we can idempotently filter for >= level and save a PO.
GET_OBJECTIVES_UP == (
    {lv | lv : requests \/ up_requests  & lv >= level} \/
    // If theres a down request above all other requests, the elevator will never be above it 
    // to catch it on the way down, so I must go up towards it.
    {lv | lv : down_requests & lv > level & !gg .(gg : ALL_OBJECTIVES => gg <= lv)}    
);

GET_OBJECTIVES_DOWN == (
    {lv | lv : requests \/ down_requests  & lv <= level} \/
    {lv | lv : up_requests & lv < level & !gg .(gg : ALL_OBJECTIVES => gg >= lv)}
);

HAS_OBJECTIVE_UP == (GET_OBJECTIVES_UP /= {});
HAS_OBJECTIVE_DOWN == (GET_OBJECTIVES_DOWN /= {});
   
CAN_CLOSE == ( (direction = kStopped &
    door = kOpen &
    door_blocked = FALSE &
    is_maintenance = FALSE &
    weight <= kMaxWeight &
    n_passengers <= kMaxPassengers));

FINISHED_DOWNWARDS_BUT_HAS_UPWARDS == (broader_direction /= kUp & not (HAS_OBJECTIVE_DOWN) & HAS_OBJECTIVE_UP & door = kClosed);

FINISHED_UPWARDS_BUT_HAS_DOWNWARDS == (broader_direction /= kDown & not ( HAS_OBJECTIVE_UP) & HAS_OBJECTIVE_DOWN & door = kClosed)
OPERATIONS

button_open =
    PRE
        direction = kStopped &
        is_maintenance = FALSE &
        door = kClosed &
        state /= kOpening
    THEN
        OpenDoor ||
        state := kClosing
    END;

button_close =
    PRE
        direction = kStopped &
        is_maintenance = FALSE &
        door = kOpen
    THEN
        IF CAN_CLOSE THEN
            CloseDoor ||
            state := kNoObjective
        END
    END;

Opening = 
PRE 
    direction = kStopped &
    door = kClosed &
    is_maintenance = FALSE &
    state = kOpening 
THEN
    OpenDoor ||
    reach_floor(level, broader_direction) ||
    IF maintenance_requested = TRUE THEN
        state := kMaintenance
    ELSE
        state := kClosing
    END
END;

Maintenance = 
PRE
    direction = kStopped &
    door = kOpen &
    state = kMaintenance
THEN
    IF is_maintenance = FALSE THEN 
        EnableMaintenance ||
        clear_all
    ELSIF maintenance_requested = FALSE THEN
        state:= kClosing ||
        DisableMaintenance
    END
END;

Closing = 
PRE 
    door = kOpen &
    direction = kStopped &
    state = kClosing
THEN
    IF maintenance_requested = TRUE THEN
        EnableMaintenance ||
        clear_all ||
        state := kMaintenance
    ELSIF CAN_CLOSE THEN
        CloseDoor ||
        state :=kNoObjective  
    ELSE
        TickDoor
    END
END;

// Stops at the nearest objective in the direction, Stop and move to NoObjective if has nowhere to go.
Working = 
PRE
    state = kWorking &
    door = kClosed &
    broader_direction /= kStopped &
    (direction = kUp => broader_direction = kUp) & 
    (direction = kDown => broader_direction = kDown) & 
    // I think this can break if someone cancels.
    (broader_direction = kUp & HAS_OBJECTIVE_UP & min(GET_OBJECTIVES_UP) /= level => CAN_MOVE_CONT(kUp)) &
    (broader_direction = kDown & HAS_OBJECTIVE_DOWN & max(GET_OBJECTIVES_DOWN) /= level => CAN_MOVE_CONT(kDown))
THEN
    IF maintenance_requested = TRUE THEN
        state := kOpening ||
        Stop
    ELSIF broader_direction = kUp & HAS_OBJECTIVE_UP THEN
        LET temp BE
            temp = min(GET_OBJECTIVES_UP)
        IN  
            ASSERT min(GET_OBJECTIVES_UP) >= level & (temp /= level => CAN_MOVE_CONT(kUp)) & temp >= level & temp: 1..kNLevels THEN 
             objective :=  temp ||
             IF temp /= level THEN
                 Move(broader_direction)
             ELSE
                 Stop || state := kOpening
             END
            END
        END 
    ELSIF broader_direction = kDown & HAS_OBJECTIVE_DOWN THEN
        LET temp BE
            temp = max(GET_OBJECTIVES_DOWN)
        IN 
            ASSERT (temp /= level => CAN_MOVE_CONT(kDown))  & temp <= level & temp : 1..kNLevels THEN 
                 objective := temp ||
                 IF temp /= level THEN
                     Move(broader_direction)
                 ELSE
                     Stop || state := kOpening
                 END
            END
        END    
    ELSE
        Stop ||
        broader_direction := kStopped ||
        state := kNoObjective
    END
END;


NoObjective = 
PRE
    direction = kStopped  &
    state = kNoObjective &
    is_maintenance = FALSE 
THEN
   // elevator stopped and wants maintenance
   IF maintenance_requested = TRUE & door = kClosed THEN
       state := kOpening
   // continue up
   ELSIF HAS_OBJECTIVE_UP & broader_direction /= kDown & door = kClosed THEN 
       state := kWorking ||
       broader_direction := kUp
   // continue down
   ELSIF HAS_OBJECTIVE_DOWN & broader_direction /= kUp & door = kClosed THEN 
       state := kWorking ||
       broader_direction := kDown  
  /* disabled for simplicity
   ELSIF  HAS_OBJECTIVE_UP & HAS_OBJECTIVE_DOWN  & door = kClosed THEN
       ASSERT broader_direction = kStopped & min(GET_OBJECTIVES_UP) >= level & max(GET_OBJECTIVES_DOWN) <= level THEN
           LET closest_up,closest_down BE 
               closest_up = min(GET_OBJECTIVES_UP) - level &
               closest_down = level - min(GET_OBJECTIVES_DOWN)
           IN 
               IF closest_up < closest_down THEN
                   broader_direction := kUp
               ELSE
                   broader_direction := kDown
               END ||
               state := kWorking
           END
       END
   */
  ELSIF FINISHED_UPWARDS_BUT_HAS_DOWNWARDS THEN
       broader_direction:= kDown ||
       state := kWorking
  ELSIF FINISHED_DOWNWARDS_BUT_HAS_UPWARDS THEN
       broader_direction:= kUp ||
       state := kWorking
  ELSIF CAN_CLOSE & ( HAS_OBJECTIVE_UP or HAS_OBJECTIVE_DOWN) THEN
       state := kClosing
    //nothing to do.
  ELSIF door = kClosed THEN
      ASSERT  (broader_direction = kUp => not (HAS_OBJECTIVE_UP)) &  (broader_direction = kDown => not (HAS_OBJECTIVE_DOWN)) THEN
           broader_direction := kStopped
      END
  END
END
    
END