MACHINE
    controller
    
INCLUDES equipments
PROMOTES
      Move,Stop,OpenDoor,CloseDoor
VARIABLES
    wants_level,
    desired_level
INVARIANT
    wants_level: BOOL &
    desired_level: 1..kNLevels
INITIALISATION
    wants_level := FALSE ||
    desired_level := 1
DEFINITIONS
    CAN_MOVE_MAIN(new_dir) == (
        new_dir: Direction & 
        weight <= kMaxWeight &
        (new_dir = direction or direction = kStopped) &
        door = kClosed &
        is_maintenance = FALSE &
        (new_dir = kUp or new_dir = kDown) &
        (new_dir = kUp => level /= (kNLevels + 1)) &
        (new_dir = kDown => level /= 1))
OPERATIONS
    RegisterElevatorClick(lv) =
    PRE
        lv : 1..kNLevels
    THEN
       desired_level:= lv ||
       wants_level := TRUE
    END;
    
    TickMain =
     
    BEGIN
        SELECT wants_level = TRUE & desired_level /= level THEN 
           ANY desired_direction WHERE
               desired_direction: Direction & desired_direction: {kUp, kDown} &
               (desired_level > level => desired_direction = kUp) &
               (desired_level < level => desired_direction = kDown) THEN
              IF CAN_MOVE_MAIN(desired_direction) THEN
                  Move(desired_direction) END
           END
        WHEN wants_level = TRUE & door = kOpen & weight <= kMaxWeight THEN
            CloseDoor
        WHEN wants_level = TRUE & desired_level = level & door = kClosed & direction = kStopped THEN
            OpenDoor   ||
            wants_level := FALSE
        END
    END
 END
    
