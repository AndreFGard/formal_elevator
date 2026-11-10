MACHINE
    main
INCLUDES
    controller
PROMOTES
    press_level, press_up, press_down,ToggleMaintenanceKey,BlockDoor,AddPassenger,RemovePassenger

DEFINITIONS
    CAN_MOVE_MAIN(new_dir) == (
    new_dir: Direction & 
    weight <= kMaxWeight &
    (new_dir = direction or direction = kStopped) &
    door = kClosed &
    is_maintenance = FALSE &
    (new_dir = kUp or new_dir = kDown) &
    (new_dir = kUp => level /= kNLevels) &
    (new_dir = kDown => level /= 1)
)

OPERATIONS
    TickMain =
    BEGIN
        IF state = kNoObjective THEN
            NoObjective
        ELSIF state = kWorking & (level /= objective => CAN_MOVE_MAIN(broader_direction)) THEN
            Working
        ELSIF state = kOpening & direction = kStopped & door = kClosed THEN
            Opening
        ELSIF state = kClosing & direction = kStopped & door = kOpen & weight <= kMaxWeight & door_blocked = FALSE THEN
            Closing
        END
    END
END
