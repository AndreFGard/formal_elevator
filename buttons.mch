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
    blinking_buttons
INVARIANT
    requests : POW(1..kNLevels) &
    up_requests : POW(1..kNLevels-1) &
    down_requests : POW(2..kNLevels) &
    press_time : valid_buttons --> NATURAL &
    leds : valid_buttons --> LedState &
    pressed_buttons : POW(valid_buttons) &
    blinking_buttons : (1..kNLevels) --> NATURAL
INITIALISATION
    requests := {} ||
    up_requests := {} ||
    down_requests := {} ||
    press_time := valid_buttons * {0} ||
    leds := valid_buttons * {OFF} ||
    pressed_buttons := {} ||
    blinking_buttons :=  (1..kNLevels) * {0}/*so internos*/
OPERATIONS
    tick_buttons = 
    LET 
        next_press_time,
        int_3,
        up_3,
        down_3
    BE
        next_press_time = press_time <+ { bb, tt | bb : pressed_buttons & tt : NATURAL & tt = press_time(bb) + 1 } &
    
        int_3 = { nn | nn : requests & (INTERNAL |-> nn) : pressed_buttons & press_time(INTERNAL |-> nn) + 1 = 3 } &
        up_3 = { nn | nn : up_requests & (UP |-> nn) : pressed_buttons & press_time(UP |-> nn) + 1 = 3 } &
        down_3 = { nn | nn : down_requests & (DOWN |-> nn) : pressed_buttons & press_time(DOWN |-> nn) + 1 = 3 }
    IN
        press_time := next_press_time <+ 
                      (({INTERNAL} * int_3) * {0}) <+ 
                      (({UP} * up_3) * {0}) <+ 
                      (({DOWN} * down_3) * {0}) ||
        up_requests := up_requests - up_3 ||
        down_requests := down_requests - down_3 ||
    
        IF int_3 /= {} THEN
            IF requests - int_3 /= {} THEN
                requests := requests - int_3 ||
                leds := leds <+ 
                        (({UP} * up_3) * {OFF}) <+ 
                        (({DOWN} * down_3) * {OFF}) <+ 
                        (({INTERNAL} * int_3) * {OFF})
            ELSE
                /*mantem todos mesmo se tiver mais de um*/
                leds := leds <+ 
                        (({UP} * up_3) * {OFF}) <+ 
                        (({DOWN} * down_3) * {OFF}) <+ 
                        (({INTERNAL} * int_3) * {BLINK})
            END
        ELSE
            leds := leds <+ 
                    (({UP} * up_3) * {OFF}) <+ 
                    (({DOWN} * down_3) * {OFF})
        END
    END;
    
    press_level(num) = 
    PRE
        num : 1..kNLevels &
        (INTERNAL|->num) /: pressed_buttons
    THEN
        requests := requests \/ {num} ||
        leds(INTERNAL |-> num) := ON ||
        pressed_buttons := pressed_buttons \/ {INTERNAL |-> num} ||
        press_time(INTERNAL |-> num) := 0
    END;

    press_up(num) = 
    PRE
        num : 1..(kNLevels - 1) &
        (UP|->num) /: pressed_buttons
    THEN
        up_requests := up_requests \/ {num} ||
        leds(UP |-> num) := ON ||
        pressed_buttons := pressed_buttons \/ {UP |-> num} ||
        press_time(UP |-> num) := 0
    END;

    press_down(num) = 
    PRE
        num : 2..kNLevels &
        (DOWN|->num) /: pressed_buttons
    THEN
        down_requests := down_requests \/ {num} ||
        leds(DOWN |-> num) := ON ||
        pressed_buttons := pressed_buttons \/ {DOWN |-> num} ||
        press_time(DOWN |-> num) := 0
    END;

    release_level(num) =
    PRE
        num : 1..kNLevels &
        (INTERNAL|->num) : pressed_buttons
    THEN
        pressed_buttons := pressed_buttons - {INTERNAL |-> num} ||
        press_time(INTERNAL |-> num) := 0
    END;

    release_up(num) =
    PRE
        num : 1..(kNLevels - 1) &
        (UP|->num) : pressed_buttons
    THEN
        pressed_buttons := pressed_buttons - {UP |-> num} ||
        press_time(UP |-> num) := 0
    END;

    release_down(num) =
    PRE
        num : 2..kNLevels &
        (DOWN|->num) : pressed_buttons
    THEN
        pressed_buttons := pressed_buttons - {DOWN |-> num} ||
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
        leds := valid_buttons * {OFF} ||
        pressed_buttons := {}
    END;
    
    reach_floor(num, bdir) =
    PRE
        num : 1..kNLevels &
        bdir : Direction
    THEN
        requests := requests - {num} ||
        IF bdir = kUp THEN
            up_requests := up_requests - {num} ||
            leds := leds <+ (({INTERNAL, UP} * {num} /\ valid_buttons) * {OFF})
        ELSIF bdir = kDown THEN
            down_requests := down_requests - {num} ||
            leds := leds <+ (({INTERNAL, DOWN} * {num} /\ valid_buttons) * {OFF})
        ELSE
            up_requests := up_requests - {num} ||
            down_requests := down_requests - {num} ||
            leds := leds <+ (({INTERNAL, UP, DOWN} * {num} /\ valid_buttons) * {OFF})
        END
    END
END