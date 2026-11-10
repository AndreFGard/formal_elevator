MACHINE
    controller
INCLUDES equipments, buttons
PROMOTES
      press_level, press_up, press_down, BlockDoor,ToggleMaintenanceKey,RemovePassenger,AddPassenger
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
    broader_direction := kUp ||
    state := kWorking ||
    objective := 1 
DEFINITIONS
CAN_MOVE_CONT(new_dir) == (
    new_dir: Direction & 
    weight <= kMaxWeight &
    (new_dir = direction or direction = kStopped) &
    door = kClosed &
    is_maintenance = FALSE &
    (new_dir = kUp or new_dir = kDown) &
    (new_dir = kUp => level /= kNLevels) &
    (new_dir = kDown => level /= 1)
);

HAS_OBJECTIVE_UP == (
   #lv .(lv : requests \/ up_requests  & lv >= level)
);
   
HAS_OBJECTIVE_DOWN == (
   #lv .(lv : requests \/ down_requests  & lv <= level)
);

GET_OBJECTIVES_UP == ({lv | lv : requests \/ up_requests  & lv >= level});
GET_OBJECTIVES_DOWN == ({lv | lv : requests \/ down_requests  & lv <= level});
   
CAN_CLOSE == ( (direction = kStopped &
    door = kOpen &
    door_blocked = FALSE &
    is_maintenance = FALSE &
    weight <= kMaxWeight))
OPERATIONS
    
Opening = 
PRE 
    direction = kStopped &
    door = kClosed &
    is_maintenance = FALSE &
    state = kOpening 
THEN
    OpenDoor ||
    reach_floor(level) ||
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
        EnableMaintenance 
    ELSIF maintenance_requested = FALSE THEN
        state:= kNoObjective ||
        DisableMaintenance
    END
END;

Closing = 
PRE 
    CAN_CLOSE &
    state = kClosing
THEN
    CloseDoor ||
    state :=kNoObjective  
END;

// Stops at the nearest objective in the direction, Stop and move to NoObjective if has nowhere to go.
Working = 
PRE
    state = kWorking &
    door = kClosed &
    broader_direction /= kStopped &
    (broader_direction = kUp & HAS_OBJECTIVE_UP & objective /= level => CAN_MOVE_CONT(kUp)) &
    (broader_direction = kDown & HAS_OBJECTIVE_DOWN & objective /= level => CAN_MOVE_CONT(kDown))
THEN
    IF broader_direction = kUp & HAS_OBJECTIVE_UP THEN
        LET temp BE
            temp = min(GET_OBJECTIVES_UP)
        IN  
            ASSERT  (requests : POW(1..kNLevels) & up_requests : POW(1..kNLevels) => GET_OBJECTIVES_UP:  POW(1..kNLevels)) &  temp >= level & temp: 1..kNLevels THEN 
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
            ASSERT temp <= level & temp : 1..kNLevels THEN 
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
   
   IF HAS_OBJECTIVE_UP & broader_direction = kUp & door = kClosed THEN
       state := kWorking ||
       broader_direction := kUp
   ELSIF HAS_OBJECTIVE_DOWN  & door = kClosed THEN
       state := kWorking ||
       broader_direction := kDown  
  ELSIF  HAS_OBJECTIVE_UP & HAS_OBJECTIVE_DOWN  & door = kClosed THEN
      state := kWorking || 
       ASSERT min(GET_OBJECTIVES_UP) >= level & max(GET_OBJECTIVES_DOWN) <= level THEN
           LET closest_up,closest_down BE 
               closest_up = min(GET_OBJECTIVES_UP) - level &
               closest_down = level - min(GET_OBJECTIVES_DOWN)
           IN 
               IF closest_up < closest_down THEN
                   broader_direction := kUp
               ELSE
                   broader_direction := kDown
               END
           END
       END
   ELSIF CAN_CLOSE & ( HAS_OBJECTIVE_UP or HAS_OBJECTIVE_DOWN) THEN
       state := kClosing
   END
END
    
END
    
