; Compute the fibonnacci sequence up to
; the representable limit of 8 bits, unsigned
Start:
  ; Start by displaying the beginning sequence
  ; of { 0, 1, 1 }
  ZERO
  DISPLAY
  ; Put 1, 1 in memory (A, B)
  ONES     ; Reg = -1
  DEC      ; Reg = -2
  NOT      ; Reg = 1
  DISPLAY
  DISPLAY
  STORE.I  ; Store A=1 and seek to B
  STORE    ; Store B=1
  SEEK -1  ; seek back to A

; Each loop iteration computes two terms
Loop:
  ADD          ; Add B
  BRANCH :Done ; Check for overflow
  DISPLAY      ; Show the value
  STORE.I      ; Store A' = A + B, seek B
  ADD          ; Add B
  BRANCH :Done ; Check for Overflow
  DISPLAY      ; Show the value
  STORE        ; Store B' = (A + B) + B
  SEEK -1      ; Seek back to A
  JUMP :Loop   ; Start again

Done:
  ZERO
Clear:
  DISPLAY
  BRANCH :Start
  JUMP :Clear