const int int32_MIN= -2147483648;
const int int32_MAX= 2147483647;

function Zabs(int x) -> int{
    if(x >= 0){
        x
    } else{
        -x
    }
}
function Always_pos(int a, int b, int c) -> int{
    if(a == 0){
        0
    }else{
        if((b * b - 4 * a * c) >= 0){
            0
        }else{
            if(a > 0){
                1
            }else{
                0
            }
        }
    }
}

function Pos_Div(int a, int b, int default) -> int{
    if(b == 0){
        default
    }else{
        let c = a / b in
        if(c < 0) {
            default
        }else{
            c
        }
        end
    }
}


function factorial(int n) -> int{
    if(n <= 0){
        1
    } else{
        n * factorial(n - 1)
    }
}

function Zgcd(int a, int b) -> int{
    if(a == 0){
        b
    } else{
        Zgcd(b, a % b)
    }
}