MACHINE
    visors
SEES
    equipments,
    controller
SETS
    DisplayMode = {
        kDisplayNormal,
        kDisplayBroken,
        kDisplayMaintenance,
        kDisplayOverweight
    }
OPERATIONS
    mode, lvl, dir <-- external_display(num) =
    PRE
        num : 1..kNLevels
    THEN
        IF is_maintenance = TRUE THEN
            mode := kDisplayMaintenance ||
            lvl := level ||
            dir := broader_direction
        ELSIF door_open_time >= 120 THEN
            mode := kDisplayBroken ||
            lvl := level ||
            dir := kStopped
        ELSE
            mode := kDisplayNormal ||
            lvl := level ||
            dir := broader_direction
        END
    END;

    mode, lvl, dir <-- internal_display =
    BEGIN
        IF is_maintenance = TRUE THEN
            mode := kDisplayMaintenance ||
            lvl := level ||
            dir := broader_direction
        ELSIF weight > kMaxWeight THEN
            mode := kDisplayOverweight ||
            lvl := level ||
            dir := broader_direction
        ELSE
            mode := kDisplayNormal ||
            lvl := level ||
            dir := broader_direction
        END
    END

END