
const BANK_INST = 0;
const BANK_DATA = 1;

const INST_TYPE_MASK = 0x80;
const INST_TYPE_REG = 0x80;
const INST_TYPE_CTRL = 0x00;

const INST_REG_SOURCE_MASK = 0x40;
const INST_REG_SOURCE_MEMORY = 0x40;
const INST_REG_SOURCE_FF = 0x00;
const INST_REG_INCREMENT_MASK = 0x01;
const INST_REG_PLANE_MASK = 0x30;
const INST_REG_PLANE_READ = 0x30;
const INST_REG_PLANE_TOGGLE = 0x20;
const INST_REG_PLANE_SET = 0x10;
const INST_REG_PLANE_UNSET = 0x00;
const INST_REG_SHIFT_MASK = 0x06;
const INST_REG_SHIFT_SHIFT = 1;

const INST_REG_READ_DEST_MASK = 0x08;
const INST_REG_READ_DEST_MEM = 0x08;
const INST_REG_READ_DEST_DISP = 0x00;
const INST_REG_TOGGLE_CARRY_MASK = 0x08;

const INST_CTRL_BANK_MASK = 0x40;
const INST_CTRL_BANK_INST = 0x00;
const INST_CTRL_BANK_MEM = 0x40;
const INST_CTRL_CONDITIONAL_MASK = 0x20;
const INST_CTRL_DELTA_MASK = 0x1F;
const INST_CTRL_DELTA_SHIFT = 0;

const NS_SVG = "http://www.w3.org/2000/svg";

var has_valid_program = false;
var mem = [
    [
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
    ],
    [
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
    ]
];
var mem_ptr = [0, 0];
var register = 0;
var condition = false;
var instruction_lines = [];

var screen = [];
var screen_buffer = [];
var complete_screens = [];

var initial_memory = [
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
];

var state = "Waiting for Program";

const NOT_RUNNING = 0;
const RUN_FOREVER = 1;
const RUN_TO_DISPLAY = 2;
const RUN_TO_FRAME = 3;

var run_type = NOT_RUNNING;

var inst_breakpoints = 0;
var mem_breakpoints = 0;

const STEP_FETCH_DATA = 1;
const STEP_DECODE_INSTRUCTION = 2;
const STEP_DISPATCH_RALU = 4;
const STEP_STORE = 8;
const STEP_DISPLAY = 16;
const STEP_FLUSH_CONDITION = 32;
const STEP_ADJUST_PTR = 64;
const NUM_STEPS = 7;

const step_durations = [
    3, // Fetch Data: 3s
    2, // Decode Instruction: 2s
    1, // Dispatch RALU: 1s
    6, // Store: 6s
    2, // Display: 2s
    2, // Flush Condition: 2s
    2, // Adjust Ptr: 2s
];

var time_into_instruction = 0;
var total_time_elapsed = 0;
var turbo_enabled = false;

function determineSteps(instruction) {
    var steps = STEP_FETCH_DATA | STEP_DECODE_INSTRUCTION;
    if ((instruction & INST_TYPE_MASK) == INST_TYPE_CTRL) {
        steps |= STEP_ADJUST_PTR;
        if (instruction & INST_CTRL_CONDITIONAL_MASK) {
            steps |= STEP_FLUSH_CONDITION;
        }
    } else {
        steps |= STEP_DISPATCH_RALU;
        if ((instruction & INST_REG_PLANE_MASK) == INST_REG_PLANE_READ) {
            if ((instruction & INST_REG_READ_DEST_MASK) == INST_REG_READ_DEST_DISP) {
                steps |= STEP_DISPLAY;
            } else {
                steps |= STEP_STORE;
                if (instruction & INST_REG_INCREMENT_MASK) {
                    steps |= STEP_ADJUST_PTR;
                }
            }
        }
    }
    return steps;
}

function determineInstTime(instruction) {
    const steps = determineSteps(instruction);
    var time = 0;
    for (var i = 0; i < NUM_STEPS; i += 1) {
        const bit = 1 << i;
        if (steps & bit) {
            time += step_durations[i];
        }
    }
    return time;
}




// ----------------------------------------------------------
// Parsing
// ----------------------------------------------------------

const PARSE_SCOPE_INST = 0;
const PARSE_SCOPE_DATA = 1;

function makeParser(code) {
    return {
        line_num: 0,
        line_pos: 0,
        lines: code.split("\n"),
        errors: [],

        scope: PARSE_SCOPE_INST,
        instructions: [], // [integer representation of instruction]
        instruction_lines: [], // [source line num for each instruction]
        labels: {}, // {lowercase_label : {line_num, inst, cased_label}
        patches: [], // { inst: integer, target_label: str }

        memory: [ // actual memory values
            0,0,0,0,0,0,0,0,
            0,0,0,0,0,0,0,0,
            0,0,0,0,0,0,0,0,
            0,0,0,0,0,0,0,0,
        ],
        memory_src: [
            null,null,null,null,null,null,null,null,
            null,null,null,null,null,null,null,null,
            null,null,null,null,null,null,null,null,
            null,null,null,null,null,null,null,null,
        ], // null | {line_num, line_pos}
        memory_labels: {}, // {lowercase_label : {line_num, address, cased_label}
        memory_address: 0, // next address to write in memory
    };
}

function peek(parser, num_chars) {
    const line = parser.lines[parser.line_num];
    return line.substring(parser.line_pos, parser.line_pos + num_chars);
}

function peek_char(parser, offset) {
    const line = parser.lines[parser.line_num];
    return line.substring(parser.line_pos + offset, parser.line_pos + offset + 1);
}

function expect(parser, str) {
    const line = parser.lines[parser.line_num];
    return line.substring(parser.line_pos).startsWith(str);
}

function advance(parser, num_chars) {
    parser.line_pos += num_chars;
}

function consume(parser, str) {
    if (expect(parser, str)) {
        advance(parser, str.length);
        return true;
    }
    return false;
}

function makeError(parser, error_str) {
    parser.errors.push({
        error: error_str,
        line_num: parser.line_num,
        line_pos: parser.line_pos,
    });
}

function consumeWhitespace(parser) {
    while (consume(parser, "\t") || consume(parser, " ")) {}
}

function parsePositiveNumberWithBase(parser, base) {
    var result = 0;
    var has_chars = false;
    var has_error = false;
    while (true) {
        const char = peek(parser, 1);

        var value = base;
        if (char >= '0' && char <= '9') {
            value = (char.charCodeAt(0) - '0'.charCodeAt(0));
        } else if (char >= 'a' && char <= 'f') {
            value = 10 + (char.charCodeAt(0) - 'a'.charCodeAt(0));
        } else if (char >= 'A' && char <= 'F') {
            value = 10 + (char.charCodeAt(0) - 'A'.charCodeAt(0));
        } else if (has_chars && char == '_') {
            advance(parser, 1);
            continue;
        } else {
            break;
        }

        if (value >= base) {
            makeError(parser, "Character invalid in base "+base+": "+char);
            has_error = true;
        }

        has_chars = true;
        advance(parser, 1);
        result *= base;
        result += value;
    }
    if (!has_chars) {
        makeError(parser, "Missing number");
        has_error = true;
    }
    if (has_error) {
        result = 0;
    }
    return result;
}

function parseNumber(parser) {
    const negative = consume(parser, "-");
    var base = 10;
    if (consume(parser, "0x")) {
        base = 16;
    } else if (consume(parser, "0b")) {
        base = 2;
    }

    var result = parsePositiveNumberWithBase(parser, base);
    if (negative) {
        result = -result;
    }
    return result;
}

function consumeWord(parser) {
    var length = 0;
    while (true) {
        const char = peek_char(parser, length);
        if (char.length == 0 || char == ':' || char == '\t' || char == ' ' || char == '/' || char == ';' || char == '.' || char == '#') break;
        length += 1;
    }
    const word = peek(parser, length);
    advance(parser, length);
    return word;
}

function consumeLabelDecl(parser) {
    const orig_pos = parser.line_pos;
    const label = consumeWord(parser);
    if (!consume(parser, ":")) {
        parser.line_pos = orig_pos; // not a label
        return;
    }

    if (label.length == 0) {
        makeError(parser, "Missing label before :");
        return;
    }

    const labels = (parser.scope == PARSE_SCOPE_INST) ? parser.labels : parser.memory_labels;

    const key = label.toLowerCase();
    if (key in labels) {
        const orig = labels[key];
        const case_note = (orig.cased_label != label) ? " Note: labels are case-insensitive." : "";
        makeError(parser, "Duplicate label '"+label+"'. Original is on line "+orig.line_num+"."+case_note);
    } else {
        labels[key] = {
            cased_label: label,
            line_num: parser.line_num,
        };
        if (parser.scope == PARSE_SCOPE_INST) {
            labels[key].inst = parser.instructions.length;
        } else {
            labels[key].address = parser.memory_address;
        }
    }
}

const instructions = {
    "add"         : INST_TYPE_REG | INST_REG_SOURCE_MEMORY | INST_REG_PLANE_TOGGLE | INST_REG_TOGGLE_CARRY_MASK,
    "dec"         : INST_TYPE_REG | INST_REG_SOURCE_FF     | INST_REG_PLANE_TOGGLE | INST_REG_TOGGLE_CARRY_MASK,
    "xor"         : INST_TYPE_REG | INST_REG_SOURCE_MEMORY | INST_REG_PLANE_TOGGLE,
    "not"         : INST_TYPE_REG | INST_REG_SOURCE_FF     | INST_REG_PLANE_TOGGLE,
    "or"          : INST_TYPE_REG | INST_REG_SOURCE_MEMORY | INST_REG_PLANE_SET,
    "ones"        : INST_TYPE_REG | INST_REG_SOURCE_FF     | INST_REG_PLANE_SET,
    "unset"       : INST_TYPE_REG | INST_REG_SOURCE_MEMORY | INST_REG_PLANE_UNSET,
    "zero"        : INST_TYPE_REG | INST_REG_SOURCE_FF     | INST_REG_PLANE_UNSET,
    "store_and"   : INST_TYPE_REG | INST_REG_SOURCE_MEMORY | INST_REG_PLANE_READ | INST_REG_READ_DEST_MEM,
    "store"       : INST_TYPE_REG | INST_REG_SOURCE_FF     | INST_REG_PLANE_READ | INST_REG_READ_DEST_MEM,
    "display_and" : INST_TYPE_REG | INST_REG_SOURCE_MEMORY | INST_REG_PLANE_READ | INST_REG_READ_DEST_DISP,
    "display"     : INST_TYPE_REG | INST_REG_SOURCE_FF     | INST_REG_PLANE_READ | INST_REG_READ_DEST_DISP,
    "jump"        : INST_TYPE_CTRL | INST_CTRL_BANK_INST,
    "branch"      : INST_TYPE_CTRL | INST_CTRL_BANK_INST | INST_CTRL_CONDITIONAL_MASK,
    "seek"        : INST_TYPE_CTRL | INST_CTRL_BANK_MEM ,
    "select"      : INST_TYPE_CTRL | INST_CTRL_BANK_MEM  | INST_CTRL_CONDITIONAL_MASK,
}

function consumeInstruction(parser) {
    const word = consumeWord(parser);
    if (word.length == 0) return; // no instruction here
    const inst_key = word.toLowerCase();
    if (inst_key in instructions) {
        var inst = instructions[inst_key];
        var has_i = false;
        var has_shr = false;
        while (consume(parser, ".")) {
            const modifier_start_pos = parser.line_pos;
            const modifier = consumeWord(parser);
            if (modifier.length == 0) {
                makeError(parser, "Missing modifier after '.'.");
            } else {
                const mod_lower = modifier.toLowerCase();
                if (mod_lower == 'i') {
                    if (inst & INST_TYPE_MASK != INST_TYPE_REG) {
                        makeError(parser, "Instruction '"+word+"' can't use modifier ."+modifier);
                    } else if (has_i) {
                        makeError(parser, "Duplicate modifier ."+modifier);
                    } else {
                        inst |= INST_REG_INCREMENT_MASK;
                        has_i = true;
                    }
                } else if (mod_lower.startsWith("shr")) {
                    const after_shr_pos = parser.line_pos;
                    parser.line_pos = modifier_start_pos + 3;
                    const shift_amt = parsePositiveNumberWithBase(parser, 10);
                    if (parser.line_pos != after_shr_pos) {
                        makeError(parser, "Invalid modifier '"+modifier+"'");
                    } else if ((inst & INST_TYPE_MASK) != INST_TYPE_REG) {
                        makeError(parser, "Instruction '"+word+"' can't use modifier ."+modifier);
                    } else if (shift_amt < 0 || shift_amt > 3) {
                        makeError(parser, ".SHR modifier can only shift 0-3 bits");
                        has_shr = true;
                    } else if (has_shr) {
                        makeError(parser, "Duplicate modifier ."+modifier.substring(0, 3));
                    } else {
                        inst |= (shift_amt << INST_REG_SHIFT_SHIFT);
                        has_shr = true;
                    }
                    parser.line_pos = after_shr_pos;
                } else {
                    makeError(parser, "Invalid modifier '"+modifier+"'");
                }
            }
        }

        if ((inst & INST_TYPE_MASK) == INST_TYPE_CTRL) {
            consumeWhitespace(parser);
            if (consume(parser, ":")) {
                const label = consumeWord(parser);
                if (label.length == 0) {
                    makeError(parser, "Missing label");
                } else {
                    parser.patches.push({ inst: parser.instructions.length, target_label: label, line_num: parser.line_num, line_pos: parser.line_pos });
                }
            } else {
                const offset = parseNumber(parser);
                if (offset < -31 || offset > 31) {
                    makeError(parser, "Offset "+offset+" is too large");
                } else {
                    inst |= (offset << INST_CTRL_DELTA_SHIFT) & INST_CTRL_DELTA_MASK;
                }
            }
        }

        parser.instructions.push(inst);
        parser.instruction_lines.push(parser.line_num);
    } else if (inst_key == "nop") {
        parser.instructions.push(0);
        parser.instruction_lines.push(parser.line_num);
    } else {
        makeError(parser, "Unknown instruction '"+word+"'");
    }
}

function consumeComment(parser) {
    if (consume(parser, "//") || consume(parser, ";") || consume(parser, "#")) {
        parser.line_pos = parser.lines[parser.line_num].length;
    }
}

function consumeScope(parser) {
    if (consume(parser, ".data")) {
        parser.scope = PARSE_SCOPE_DATA;
        consumeWhitespace(parser);
        consumeComment(parser);
        if (parser.line_pos < parser.lines[parser.line_num].length) {
            parser.memory_address = parseNumber(parser);
            if (parser.memory_address < 0 || parser.memory_address > 31) {
                makeError(parser, ".data scope has invalid address, must be between 0 and 31.");
                parser.memory_address = 0;
            }
            consumeWhitespace(parser);
            consumeComment(parser);
        }
        return true;
    } else if (consume(parser, ".inst")) {
        parser.scope = PARSE_SCOPE_INST;
        consumeWhitespace(parser);
        consumeComment(parser);
        return true;
    }
    return false;
}

function parseMemoryValue(parser) {
    const pos = parser.line_pos;
    var value = parseNumber(parser);
    if (value < -255 || value > 255) {
        makeError(parser, "Memory value "+value+" cannot be represented in 8 bits!");
    }
    value = value & 0xFF;
    const prev_src = parser.memory_src[parser.memory_address];
    if (prev_src) {
        makeError(parser, "Memory address "+parser.memory_address+" was specified twice! First at "+(prev_src.line_num+1)+":"+(prev_src.line_pos+1)+".");
    } else {
        parser.memory_src[parser.memory_address] = {
            line_num: parser.line_num,
            line_pos: pos,
        };
        parser.memory[parser.memory_address] = value;
    }
    parser.memory_address += 1;
    if (parser.memory_address >= 32) {
        parser.memory_address = 0;
    }
}

function applyLabelPatches(parser) {
    for (const patch of parser.patches) {
        const label_key = patch.target_label.toLowerCase();
        if (label_key in parser.labels) {
            const target_inst = parser.labels[label_key].inst;
            const patch_inst = patch.inst;
            const delta = target_inst - patch_inst - 1;
            parser.instructions[patch_inst] |= ((delta << INST_CTRL_DELTA_SHIFT) & INST_CTRL_DELTA_MASK)
        } else {
            parser.errors.push({
                error: "Couldn't find label declaration for '"+patch.target_label+"'",
                line_num: patch.line_num,
                line_pos: patch.line_pos,
            });
        }
    }
}

function fillInstructions(parser) {
    if (parser.instructions.length > 32) {
        makeError(parser, "Program has more than 32 instructions ("+parser.instructions.length+")");
    } else {
        while (parser.instructions.length < 32) {
            parser.instructions.push(0);
        }
    }
}

function parseProgram(parser) {
    var index = 0;
    while (index < parser.lines.length) {
        parser.line_num = index;
        parser.line_pos = 0;

        consumeWhitespace(parser);

        if (!consumeScope(parser)) {
            consumeLabelDecl(parser);
            if (parser.scope == PARSE_SCOPE_INST) {
                consumeWhitespace(parser);
                consumeInstruction(parser);
                consumeWhitespace(parser);
                consumeComment(parser);
            } else if (parser.scope == PARSE_SCOPE_DATA) {
                while (true) {
                    consumeWhitespace(parser);
                    consumeComment(parser);
                    if (parser.line_pos >= parser.lines[parser.line_num].length) break;
                    parseMemoryValue(parser);
                }
            }
        }

        if (parser.line_pos < parser.lines[parser.line_num].length) {
            makeError(parser, "Unexpected extra arguments");
        }

        index += 1;
    }

    parser.line_num = -1;
    parser.line_pos = 0;

    applyLabelPatches(parser);

    fillInstructions(parser);
}




function execInst() {
    const inst = mem[BANK_INST][mem_ptr[BANK_INST]];
    mem_ptr[BANK_INST] = (mem_ptr[BANK_INST] + 1) % 32;

    if (inst & INST_TYPE_MASK) {
        var operand = (inst & INST_REG_SOURCE_MASK) ? mem[BANK_DATA][mem_ptr[BANK_DATA]] : 0xFF;
        const orig = register;
        const shift = (inst & INST_REG_SHIFT_MASK) >> INST_REG_SHIFT_SHIFT;
        operand = operand >> shift;
        switch (inst & INST_REG_PLANE_MASK) {
            case INST_REG_PLANE_UNSET:
                register &= ~operand;
                condition = (register == orig);
                break;
            case INST_REG_PLANE_SET:
                register |= operand;
                condition = (register == orig);
                break;
            case INST_REG_PLANE_TOGGLE:
                if (inst & INST_REG_TOGGLE_CARRY_MASK) {
                    register += operand;
                    condition = register > 0xFF;
                    register = register & 0xFF;
                } else {
                    register ^= operand;
                    condition = !!((orig & 0x80) && (operand & 0x80));
                }
                break;
            case INST_REG_PLANE_READ:
                const value = (register & operand);
                if (inst & INST_REG_READ_DEST_MASK) {
                    mem[BANK_DATA][mem_ptr[BANK_DATA]] = value;
                    condition = false;
                } else {
                    condition = outputToScreen(value);
                }
                break;
        }
        if (inst & INST_REG_INCREMENT_MASK) {
            mem_ptr[BANK_DATA] = (mem_ptr[BANK_DATA] + 1) % 32;
        }
    } else {
        if (condition || !(inst & INST_CTRL_CONDITIONAL_MASK)) {
            const bank = (inst & INST_CTRL_BANK_MASK) ? BANK_DATA : BANK_INST;
            const delta = (inst & INST_CTRL_DELTA_MASK) >> INST_CTRL_DELTA_SHIFT;
            mem_ptr[bank] = (mem_ptr[bank] + delta) % 32;
        }
    }
}

function outputToScreen(value) {
    if (run_type == RUN_TO_DISPLAY) {
        cancelRun();
        state = "Paused (Display)"
    }

    screen_buffer.push(value);
    if (screen_buffer.length < 8) return false;

    if (run_type == RUN_TO_FRAME) {
        cancelRun();
        state = "Paused (Frame)"
    }

    if (screen.length != 0) {
        complete_screens.push(screen);
    }
    screen = screen_buffer;
    screen_buffer = [];
    return true;
}

function formatValueAll(value) {
    var result = "0x"+value.toString(16).padStart(2, '0') + '\u00a0' +
                 "0b"+value.toString(2).padStart(8, '0') +
                 value.toString().padStart(4, '\u00a0');
    if (value & 0x80) {
        result += (value - 256).toString().padStart(5, '\u00a0');
    } else {
        result += "".padStart(5, '\u00a0')
    }
    return result;
}

function updateScreenRows(group, rows) {
    group.innerHTML = "";
    const numRows = Math.min(8, rows.length);
    for (var i = 0; i < numRows; i += 1) {
        const y = 7 - i;
        for (var j = 0; j < 8; j += 1) {
            const x = 7 - j;
            const bit = 1 << j;
            const marble = document.createElementNS(NS_SVG, "circle");
            marble.setAttributeNS(null, "cx", x.toString());
            marble.setAttributeNS(null, "cy", y.toString());
            marble.setAttributeNS(null, "r", "0.475");
            const color = rows[i] & bit ? "white" : "black";
            marble.setAttributeNS(null, "fill", color);
            group.appendChild(marble);
        }
    }
}

function updateDisplayedState() {
    if (!has_valid_program) return;

    const state_disp = document.getElementById("ctrl-state");
    state_disp.textContent = state;

    const dreg = document.getElementById("ctrl-register");
    dreg.textContent = formatValueAll(register);

    const dcond = document.getElementById("ctrl-condition");
    dcond.textContent = condition.toString();

    const ddptr = document.getElementById("ctrl-dataptr");
    ddptr.textContent = mem_ptr[BANK_DATA].toString();

    const diptr = document.getElementById("ctrl-instptr");
    diptr.textContent = mem_ptr[BANK_INST].toString();

    var addr = 0;
    while (addr < 32) {
        const val = document.getElementById("ctrl-mem-"+addr.toString());
        val.textContent = formatValueAll(mem[BANK_DATA][addr]);

        const f = "ctrl-mem-row-"+addr.toString();
        const data_row = document.getElementById(f);
        if (addr == mem_ptr[BANK_DATA]) {
            data_row.classList.add("mem-pointee");
        } else {
            data_row.classList.remove("mem-pointee");
        }

        const inst_row = document.getElementById("ctrl-inst-row-"+addr.toString());
        if (inst_row) {
            if (addr == mem_ptr[BANK_INST]) {
                inst_row.classList.add("mem-pointee");
            } else {
                inst_row.classList.remove("mem-pointee");
            }
        }

        addr += 1;
    }

    const frontbuffer = document.getElementById("screen-front-body");
    updateScreenRows(frontbuffer, screen);

    const backbuffer = document.getElementById("screen-back-body");
    updateScreenRows(backbuffer, screen_buffer);

    const screen_history = document.getElementById("screen-history");
    while (complete_screens.length > 0) {
        const rows = complete_screens.pop();
        const screen = document.createElementNS(NS_SVG, "svg");
        screen.setAttributeNS(null, "viewBox", "-0.6 -0.6 8.2 8.2");
        screen.setAttributeNS(null, "class", "screen");
        updateScreenRows(screen, rows);
        screen_history.insertBefore(screen, screen_history.firstChild)
    }

    var inst_steps = 0;
    if (has_valid_program) {
        const next_inst = mem[BANK_INST][mem_ptr[BANK_INST]];
        inst_steps = determineSteps(next_inst);
    }

    var time_left = time_into_instruction;
    for (var i = 0; i < NUM_STEPS; i += 1) {
        const bit = 1 << i;
        const bar = document.getElementById("exec-step-"+i.toString());
        if (inst_steps & bit) {
            bar.classList.remove("disabled");
            if (time_left < step_durations[i]) {
                const percent = 100 * time_left / step_durations[i];
                bar.firstElementChild.style.width = percent + "%";
                time_left = 0;
            } else {
                bar.firstElementChild.style.width = "100%";
                time_left -= step_durations[i];
            }
        } else {
            bar.classList.add("disabled");
        }
    }

    const uptime_elem = document.getElementById("exec-uptime");
    var uptime_seconds = total_time_elapsed + time_into_instruction;
    const has_days = uptime_seconds > 24 * 60 * 60;
    const has_hours = uptime_seconds > 60 * 60;
    const has_minutes = uptime_seconds > 60;
    var uptime_str = "";
    if (has_days) {
        uptime_str += Math.floor(uptime_seconds / (24 * 60 * 60)).toString() + "d ";
        uptime_seconds %= (24 * 60 * 60);
    }
    if (has_hours) {
        uptime_str += Math.floor(uptime_seconds / (60 * 60)).toString().padStart(2, "0") + ":";
        uptime_seconds %= (60 * 60);
    }
    if (has_minutes) {
        uptime_str += Math.floor(uptime_seconds / (60)).toString().padStart(2, "0") + ":";
        uptime_seconds %= (60);
    }
    uptime_str += uptime_seconds.toFixed(1).padStart(4, "0");
    uptime_elem.innerText = uptime_str;
}

var last_tick_time_ms;

function runStep() {
    if (!has_valid_program) return;
    if (run_type == NOT_RUNNING) return;

    const tick_time_ms = Date.now();
    const delta_ms = Math.max(0, Math.min(tick_time_ms - last_tick_time_ms, 100));
    last_tick_time_ms = tick_time_ms;

    var speed = Number(document.getElementById("ctrl-speed").value);
    if (typeof speed !== "number" || isNaN(speed)) speed = 1;
    if (turbo_enabled) speed *= 100;
    speed = Math.min(Math.max(speed, 1), 10000);

    const elapsed_time = speed * delta_ms / 1000;

    time_into_instruction += elapsed_time;

    while (run_type != NOT_RUNNING) {
        const next_inst = mem[BANK_INST][mem_ptr[BANK_INST]];
        const inst_time = determineInstTime(next_inst);
        if (time_into_instruction >= inst_time) {
            time_into_instruction -= inst_time;
            total_time_elapsed += inst_time;
            execInst();
            checkBreakpoints();
        } else {
            break;
        }
    }

    updateDisplayedState();

    if (run_type != NOT_RUNNING) {
        window.requestAnimationFrame(runStep);
    }
}

function checkBreakpoints() {
    // Check breakpoints
    if (run_type != NOT_RUNNING) {
        if (inst_breakpoints & (1 << mem_ptr[BANK_INST])) {
            cancelRun();
            state = "Paused (Breakpoint)"
        }

        if (mem_breakpoints & (1 << mem_ptr[BANK_DATA])) {
            // Memory breakpoints only break on a store instruction
            const next_inst = mem[BANK_INST][mem_ptr[BANK_INST]];
            const store_bit_fields = INST_TYPE_MASK | INST_REG_PLANE_MASK | INST_REG_READ_DEST_MASK;
            const store_bit_values = INST_TYPE_REG | INST_REG_PLANE_READ | INST_REG_READ_DEST_MEM;
            if ((next_inst & store_bit_fields) == store_bit_values) {
                cancelRun();
                state = "Paused (Memory Breakpoint)"
            }
        }
    }    
}

function startRunning() {
    last_tick_time_ms = Date.now();
    window.requestAnimationFrame(runStep);
}

function cancelRun() {
    run_type = NOT_RUNNING;
    time_into_instruction = 0;
}

function pauseRun() {
    run_type = NOT_RUNNING;
}

function btnStep() {
    if (!has_valid_program) return;

    cancelRun();
    state = "Paused (Step)"

    const next_inst = mem[BANK_INST][mem_ptr[BANK_INST]];
    const inst_time = determineInstTime(next_inst);
    total_time_elapsed += inst_time;
    execInst();

    time_into_instruction = 0;

    updateDisplayedState();
}

function btnRun() {
    if (!has_valid_program) return;

    run_type = RUN_FOREVER;
    state = "Running";
    startRunning();
}

function btnNextFrame() {
    if (!has_valid_program) return;

    run_type = RUN_TO_FRAME;
    state = "Running to next frame"
    startRunning();
}

function btnNextDisplay() {
    if (!has_valid_program) return;

    run_type = RUN_TO_DISPLAY;
    state = "Running to next display"
    startRunning();
}

function btnPause() {
    if (!has_valid_program) return;

    if (run_type != NOT_RUNNING) {
        pauseRun();
        state = "Paused"
        updateDisplayedState();
    }
}

function btnReset() {
    if (!has_valid_program) return;

    cancelRun();
    state = "Paused (Reset)";

    total_time_elapsed = 0;

    register = 0;
    condition = false;
    mem_ptr = [0, 0];

    for (let i = 0; i < 32; i++) {
        mem[BANK_DATA][i] = initial_memory[i];
    }

    complete_screens = [];
    screen_buffer = [];
    screen = [];

    const screen_history = document.getElementById("screen-history");
    screen_history.innerHTML = "";

    updateDisplayedState();
}

function btnToggleBackbuffer() {
    const backbuffer = document.getElementById("screen-back-body");
    if (backbuffer.getAttributeNS(null, "filter")) {
        backbuffer.setAttributeNS(null, "filter", "");
    } else {
        backbuffer.setAttributeNS(null, "filter", "url(#blurred)");
    }
}

function assembleProgramAndShowErrors() {
    const code = document.getElementById("src-program").value;
    const parser = makeParser(code);
    parseProgram(parser);

    const errors = document.getElementById("src-errors");
    errors.innerHTML = "";
    if (parser.errors.length != 0) {
        for (const err of parser.errors) {
            if (err.line_num == -1) {
                const line = document.createElement("div");
                line.textContent = err.error;
                errors.appendChild(line);
            }
        }
        for (const err of parser.errors) {
            if (err.line_num != -1) {
                const line = document.createElement("div");
                line.textContent = (err.line_num+1)+":"+(err.line_pos+1)+" "+err.error;
                errors.appendChild(line);
            }
        }
    }

    return {
        success: parser.errors.length == 0,
        lines: parser.lines,
        instructions: parser.instructions,
        instruction_lines: parser.instruction_lines,
        labels: parser.labels,
        memory: parser.memory,
        memory_labels: parser.memory_labels,
    };
}

function btnAssembleProgram() {
    assembleProgramAndShowErrors();
}

function btnToggleInstBreakpoint(index, elem) {
    const bit = 1 << index;
    if (inst_breakpoints & bit) {
        elem.classList.remove("mem-breakpoint");
        inst_breakpoints &= ~bit;
    } else {
        elem.classList.add("mem-breakpoint");
        inst_breakpoints |= bit;
    }
}

function btnToggleMemBreakpoint(index, elem) {
    const bit = 1 << index;
    if (mem_breakpoints & bit) {
        elem.classList.remove("mem-breakpoint");
        mem_breakpoints &= ~bit;
    } else {
        elem.classList.add("mem-breakpoint");
        mem_breakpoints |= bit;
    }
}

function makeOnInstRowClick(idx, elem) {
    return () => btnToggleInstBreakpoint(idx, elem);
}

function btnLoadProgram() {
    const result = assembleProgramAndShowErrors();

    if (result.success) {
        const code_block = document.getElementById("ctrl-program");
        code_block.innerHTML = "";
        
        var idx = 0;
        for (const inst of result.instructions) {
            const line = document.createElement("tr");
            line.onclick = makeOnInstRowClick(idx, line);
            line.id = "ctrl-inst-row-"+idx.toString();
            const cell_idx = document.createElement("td");
            cell_idx.classList.add("mem-address");
            cell_idx.textContent = idx.toString();
            line.appendChild(cell_idx);
            const bits = document.createElement("td");
            bits.textContent = inst.toString(2).padStart(8, '0');
            line.appendChild(bits);
            const labels = document.createElement("td");
            labels.id = "ctrl-inst-labels-"+idx.toString();
            line.appendChild(labels);
            const text = document.createElement("td");
            if (idx < result.instruction_lines.length) {
                text.textContent = result.lines[result.instruction_lines[idx]].trim().replaceAll(" ", "\u00a0");
            } else {
                text.textContent = "NOP";
            }
            line.appendChild(text);
            code_block.appendChild(line);
            idx += 1;
        }

        for (const label_key in result.labels) {
            const label = result.labels[label_key];
            document.getElementById("ctrl-inst-labels-"+label.inst.toString()).append(label.cased_label+":")
        }

        for (var i = 0; i < 32; i += 1) {
            document.getElementById("ctrl-mem-labels-"+i.toString()).innerHTML = "";
        }

        for (const label_key in result.memory_labels) {
            const label = result.memory_labels[label_key];
            document.getElementById("ctrl-mem-labels-"+label.address.toString()).append(label.cased_label+":")
        }

        instruction_lines = result.instruction_lines;
        mem[BANK_INST] = result.instructions;
        initial_memory = result.memory;
        has_valid_program = true;

        btnReset();
    }
}

document.addEventListener("DOMContentLoaded", function() {
    {
        for (var index = 0; index < 32; index += 1) {
            {
                const mem_display = document.getElementById("ctrl-mem-row-"+index);
                const capture_idx = index;
                mem_display.onclick = () => {
                    btnToggleMemBreakpoint(capture_idx, mem_display);
                };
            }
        }
    }

    {
        window.addEventListener('mouseup', () => { turbo_enabled = false; });
        document.getElementById("ctrl-turbo").addEventListener('mouseup', () => { turbo_enabled = false; });
        document.getElementById("ctrl-turbo").addEventListener('mousedown', () => { turbo_enabled = true; });
    }
});
