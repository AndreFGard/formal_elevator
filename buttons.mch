MACHINE
    buttons
SEES
    equipments
SETS
    ButtonType = {INTERNAL, UP, DOWN}
CONSTANTS
    valid_buttons
PROPERTIES
    valid_buttons = ({INTERNAL} * (1..kNLevels)) \/ 
                    ({UP} * (1..kNLevels-1)) \/ 
                    ({DOWN} * (2..kNLevels))
VARIABLES
    requests,
    up_requests,
    down_requests,
    press_time,
    leds,
    pressed_buttons,
    kTwoSecondBlink
INVARIANT
    requests : POW(1..kNLevels) &
    up_requests : POW(1..kNLevels-1) &
    down_requests : POW(2..kNLevels) &
    press_time : valid_buttons --> NATURAL &
    leds : valid_buttons --> LedState &
    pressed_buttons : POW(valid_buttons) &
    kTwoSecondBlink : BOOL
INITIALISATION
    requests := {} ||
    up_requests := {} ||
    down_requests := {} ||
    press_time := valid_buttons * {0} ||
    leds := valid_buttons * {OFF} ||
    pressed_buttons := {} ||
    kTwoSecondBlink := FALSE
OPERATIONS
    tick_buttons = 
    BEGIN
        press_time := press_time <+ { bb, tt | bb : pressed_buttons & tt = press_time(bb) + 1 }
    END;
    
    press_level(num) = 
    PRE
        num : 1..kNLevels
    THEN
        requests := requests \/ {num} ||
        leds(INTERNAL |-> num) := ON ||
        pressed_buttons := pressed_buttons \/ {INTERNAL |-> num} ||
        press_time(INTERNAL |-> num) := 0
    END;

    press_up(num) = 
    PRE
        num : 1..(kNLevels - 1)
    THEN
        up_requests := up_requests \/ {num} ||
        leds(UP |-> num) := ON ||
        pressed_buttons := pressed_buttons \/ {UP |-> num} ||
        press_time(UP |-> num) := 0
    END;

    press_down(num) = 
    PRE
        num : 2..kNLevels
    THEN
        down_requests := down_requests \/ {num} ||
        leds(DOWN |-> num) := ON ||
        pressed_buttons := pressed_buttons \/ {DOWN |-> num} ||
        press_time(DOWN |-> num) := 0
    END;

    release_level(num) =
    PRE
        num : 1..kNLevels
    THEN
        pressed_buttons := pressed_buttons - {INTERNAL |-> num} ||
        press_time(INTERNAL |-> num) := 0
    END;

    release_up(num) =
    PRE
        num : 1..(kNLevels - 1)
    THEN
        pressed_buttons := pressed_buttons - {UP |-> num} ||
        press_time(UP |-> num) := 0
    END;

    release_down(num) =
    PRE
        num : 2..kNLevels
    THEN
        pressed_buttons := pressed_buttons - {DOWN |-> num} ||
        press_time(DOWN |-> num) := 0
    END;

    cancel_level(num) = 
    PRE
        num : 1..kNLevels &
        num : requests &
        (INTERNAL |-> num) : pressed_buttons &
        press_time(INTERNAL |-> num) >= 3
    THEN
        IF card(requests) > 1 THEN
            requests := requests - {num} ||
            leds(INTERNAL |-> num) := OFF ||
            press_time(INTERNAL |-> num) := 0
        ELSE
            leds(INTERNAL |-> num) := BLINK ||
            press_time(INTERNAL |-> num) := 0 ||
            kTwoSecondBlink := TRUE
        END
    END;

    cancel_up(num) = 
    PRE
        num : 1..(kNLevels - 1) &
        num : up_requests &
        (UP |-> num) : pressed_buttons &
        press_time(UP |-> num) >= 3
    THEN
        up_requests := up_requests - {num} ||
        leds(UP |-> num) := OFF ||
        press_time(UP |-> num) := 0
    END;

    cancel_down(num) = 
    PRE
        num : 2..kNLevels &
        num : down_requests &
        (DOWN |-> num) : pressed_buttons &
        press_time(DOWN |-> num) >= 3
    THEN
        down_requests := down_requests - {num} ||
        leds(DOWN |-> num) := OFF ||
        press_time(DOWN |-> num) := 0
    END;
    
    ans <-- get_pending_cancel_levels = 
    BEGIN
        ans := { num | num : requests & (INTERNAL |-> num) : pressed_buttons & press_time(INTERNAL |-> num) >= 3 }
    END;

    ans <-- get_pending_cancel_ups = 
    BEGIN
        ans := { num | num : up_requests & (UP |-> num) : pressed_buttons & press_time(UP |-> num) >= 3 }
    END;

    ans <-- get_pending_cancel_downs = 
    BEGIN
        ans := { num | num : down_requests & (DOWN |-> num) : pressed_buttons & press_time(DOWN |-> num) >= 3 }
    END;
    
    clear_all = 
    BEGIN
        requests := {} ||
        up_requests := {} ||
        down_requests := {} ||
        press_time := valid_buttons * {0} ||
        leds := valid_buttons * {OFF}
    END;
    
    reach_floor(num) =
    PRE
        num : 1..kNLevels
    THEN
        requests := requests - {num} ||
        IF direction = kUp THEN
            up_requests := up_requests - {num} ||
            leds := leds <+ (({INTERNAL, UP} * {num} /\ valid_buttons) * {OFF})
        ELSIF direction = kDown THEN
            down_requests := down_requests - {num} ||
            leds := leds <+ (({INTERNAL, DOWN} * {num} /\ valid_buttons) * {OFF})
        ELSE
            up_requests := up_requests - {num} ||
            down_requests := down_requests - {num} ||
            leds := leds <+ (({INTERNAL, UP, DOWN} * {num} /\ valid_buttons) * {OFF})
        END
    END
END