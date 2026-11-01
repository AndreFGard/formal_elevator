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
        SELECT wants_level = TRUE & door = kClosed & desired_level /= level THEN        
           ANY desired_direction WHERE
               desired_direction: Direction &
               (desired_level > level => desired_direction = kUp) &
               (desired_level < level => desired_direction = kDown) THEN
               Move(desired_direction)
           END
        WHEN wants_level = TRUE & door = kOpen THEN
            CloseDoor
        WHEN wants_level = TRUE & desired_level = level & door = kClosed THEN
            OpenDoor   ||
            wants_level := FALSE
        END
    END
 END
    
