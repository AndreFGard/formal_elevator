MACHINE
    visors
SEES
    controller
SETS
    DisplayMode = {
        kDisplayNormal,
        kDisplayBroken,
        kDisplayMaintenance,
        kDisplayOverweight
    }
VARIABLES
    ext_mode,
    int_mode,
    visor_level,
    visor_dir
INVARIANT
    ext_mode : DisplayMode &
    int_mode : DisplayMode &
    visor_level : 1..kNLevels &
    visor_dir : Direction
INITIALISATION
    ext_mode := kDisplayNormal ||
    int_mode := kDisplayNormal ||
    visor_level := 1 ||
    visor_dir := kStopped
OPERATIONS
    tick_visors =
    BEGIN
        visor_level := level ||
        
        IF is_maintenance = TRUE or door_open_time >= kMaxDoorOpenTime THEN
            visor_dir := kStopped
        ELSE
            visor_dir := broader_direction
        END ||

        IF is_maintenance = TRUE THEN
            ext_mode := kDisplayMaintenance
        ELSIF door_open_time >= kMaxDoorOpenTime THEN
            ext_mode := kDisplayBroken
        ELSE
            ext_mode := kDisplayNormal
        END ||

        IF is_maintenance = TRUE THEN
            int_mode := kDisplayMaintenance
        ELSIF ((weight > kMaxWeight) or (n_passengers > kMaxPassengers)) THEN
            int_mode := kDisplayOverweight
        ELSE
            int_mode := kDisplayNormal
        END
    END
END