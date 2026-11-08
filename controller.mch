MACHINE
    controller
INCLUDES equipments, buttons
PROMOTES
      press_level, press_up, press_down
SETS
    MainState = {kNoObjective, kWorking,kClosing,kOpening,kWaitingBoarding}
VARIABLES
    broader_direction,
    state,
    objective
INVARIANT
    broader_direction : Direction &
    state: MainState &
    objective : 1..kNLevels &
    
    (state = kNoObjective => direction = kStopped) &
    (broader_direction = kStopped => state /= kWorking)
    
INITIALISATION
    broader_direction :=    kStopped ||
    state := kNoObjective ||
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
)
   
OPERATIONS
    
Opening = 
PRE 
    direction = kStopped &
    door = kClosed &
    state = kOpening 
THEN
    OpenDoor ||
    state := kClosing
END;

Closing = 
PRE 
    direction = kStopped &
    door = kOpen &
    state = kClosing  &
    weight <= kMaxWeight
THEN
    CloseDoor ||
    reach_floor(level) ||
    state :=kNoObjective  
END;

// has objective, always takes 1 tick.
Working = 
PRE
    state = kWorking &
    broader_direction /= kStopped &
    (level /= objective => CAN_MOVE_CONT(broader_direction))
THEN
    IF (level /= objective) THEN
        Move(broader_direction)
    ELSE 
        Stop ||
        state := kOpening
    END
END;


UpdateObjective = 
PRE
    direction = kStopped  &
    state = kNoObjective
THEN
    IF broader_direction = kUp & HAS_OBJECTIVE_UP THEN
        LET above_me, temp BE
            above_me = {lv | lv : requests \/ up_requests  & lv >= level} &
            temp = min(above_me)
        IN  
            ASSERT temp >= level & temp: 1..kNLevels THEN 
             objective :=  temp ||
             state := kWorking
            END
        END 
    ELSIF broader_direction = kDown & HAS_OBJECTIVE_DOWN THEN
        LET below,temp BE
            below = {lv | lv : requests \/ down_requests  & lv <= level} &
            temp = max(below)
        IN 
            ASSERT temp <= level & temp : 1..kNLevels THEN 
                objective := temp ||
                state := kWorking
            END
        END
    ELSE
        LET options BE
            options = requests \/ down_requests \/ up_requests
        IN
            ASSERT options : POW(1..kNLevels) THEN
                IF card(options) > 0 THEN
                    objective:= min(options) ||
                    IF min(options) < level THEN
                        broader_direction := kDown ||
                        state := kWorking
                    ELSIF min(options) > level THEN
                        broader_direction := kUp ||
                        state := kWorking
                    ELSE 
                        broader_direction := kStopped ||
                        state := kOpening
                    END
                 ELSE 
                    broader_direction := kStopped
                END       
            END
        END
    END
END
    
END
    
