MACHINE
    main
INCLUDES
    controller, visors
PROMOTES
    press_level, press_up,         press_down,ToggleMaintenanceKey,BlockDoor,AddPassenger,RemovePassenger,
    release_level, release_up, release_down,
    button_open, button_close, UnblockDoor
SETS
    CyclePhase = {MAIN, VISORS, BUTTONS}
VARIABLES
    exception,
    phase
INVARIANT
    exception : BOOL & 
    exception = FALSE &
    phase : CyclePhase
INITIALISATION
    exception := FALSE ||
    phase := MAIN
DEFINITIONS
    CAN_MOVE_MAIN(new_dir) == (
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

// Mirrors of controller's definitions (DEFINITIONS are not exported by INCLUDES).
ALL_MAIN == (requests \/ up_requests \/ down_requests);

GET_UP_MAIN == (
    {lv | lv : requests \/ up_requests & lv >= level} \/
    {lv | lv : down_requests & lv >= level & !gg .(gg : ALL_MAIN => gg <= lv)}
);

GET_DOWN_MAIN == (
    {lv | lv : requests \/ down_requests & lv <= level} \/
    {lv | lv : up_requests & lv <= level & !gg .(gg : ALL_MAIN => gg >= lv)}
);

HAS_UP_MAIN == (GET_UP_MAIN /= {});
HAS_DOWN_MAIN == (GET_DOWN_MAIN /= {});

TARGET_UP_MAIN == min(GET_UP_MAIN);
TARGET_DOWN_MAIN == max(GET_DOWN_MAIN)

OPERATIONS
    TickMain =
    PRE
        phase = MAIN
    THEN
        IF state = kNoObjective THEN
            NoObjective
        ELSIF state = kWorking &
              (broader_direction = kUp & HAS_UP_MAIN & TARGET_UP_MAIN /= level => CAN_MOVE_MAIN(broader_direction)) &
              (broader_direction = kDown & HAS_DOWN_MAIN & TARGET_DOWN_MAIN /= level => CAN_MOVE_MAIN(broader_direction)) THEN
            Working
        ELSIF state = kOpening & direction = kStopped & door = kClosed THEN
            Opening
        ELSIF state = kClosing THEN
            Closing
        ELSIF state = kMaintenance & direction = kStopped & door = kOpen THEN
            Maintenance
        ELSE
            exception := TRUE
        END ||
        phase := VISORS
    END;
    
    TickVisors =
    PRE
        phase = VISORS
    THEN
        tick_visors ||
        phase := BUTTONS
    END;
    
    TickButtons =
    PRE
        phase = BUTTONS
    THEN
        tick_buttons ||
        phase := MAIN
    END
    
END