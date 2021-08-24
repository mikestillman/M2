--m1 code in enr.d10

ring r
43
5
vwxyz
;
;
ideal alpha
10
16v2-2xy-wz
16w2-vx-2yz 
16x2-wy-2vz 
-2vw+16y2-xz 
-2wx-vy+16z2 
4v2+16xy-wz
4w2-vx+16yz 
4x2-wy+16vz 
16vw+4y2-xz 
16wx-vy+4z2 
 
betti alpha
setdegs alpha
-2:2
;

nres alpha falpha
betti falpha

% betti falpha
; total:      1    10    25    31    20     5 
; --------------------------------------------
;    -2:      1     -     -     -     -     - 
;    -1:      -    10    15     5     -     - 
;     0:      -     -    10    26    20     5 

nres r kos
betti kos
dsum kos.5 kos.5 kos5m2
transpose kos5m2 tkos5m2
setdegs tkos5m2
-2:2
;
random 2 5 ran
submat falpha.3 aaa
;
1..5
transpose aaa taaa
mult ran taaa bbb
setdegs bbb
-2
;
lift-std tkos5m2 stkos5m2
lift stkos5m2 bbb tphi
betti tphi

transpose falpha.3 tpresg
<stack dir tphi tpresg
setdegs dir
-1:10 -2:5 -3:26
;
nres dir fdir
betti fdir

flatten fdir.2 i
nres i fi 
betti fi

; total:      1    15    29    20     5 
; --------------------------------------
;     0:      1     -     -     -     - 
;     1:      -     -     -     -     - 
;     2:      -     -     -     -     - 
;     3:      -     -     -     -     - 
;     4:      -     5     3     -     - 
;     5:      -    10    26    20     5 

hilb fi.1

; codimension = 2
; degree      = 11
; genus       = 10



