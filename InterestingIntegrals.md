# Inside Interesting Integrals

This is a list of numbered integrals (and other formulas) appearing in the textbook *Inside Interesting Integrals*.

## Chapter 1: Introduction (2/9)


| Section |    Type    |                                     Expression                                     |                                            Status                                            |
| :-----: | :--------: | :--------------------------------------------------------------------------------: | :------------------------------------------------------------------------------------------: |
|   1.5   |  Integral  |                    $\int_0^\infty \frac{\ln{x}}{x^2+1} dx = 0$                    |                                             Done                                             |
|   1.6   |  Integral  |  $\int_0^1 \frac 1 {\left[ax + b(1-x)\right]^2}dx = \frac 1{ab}$ <br> for $ab>0$  | [Overly stringent conditions](#Overly_Stringent_Conditions) <br> Notice the proof is in 3.10 |
|   1.6   |  Integral  |          $P.V. \int_0^\infty \frac{1}{x ^ 3 - 1} dx = -\frac{\pi\sqrt3}9$          |                      [Cauchy principle value](#Cauchy_Principle_Value)                      |
|   1.7   |  Integral  |         $\int_0^1 \frac{x^4 (1 - x) ^ 4}{1 + x^2}dx = \frac{22}{7} - \pi$         |                                             Done                                             |
|   1.8   |  Integral  | $\int_0^\infty \frac{\left\{x\right\}-\frac{1}{2}}{x} dx = -1 + \ln{\sqrt{2 \pi}}$ |                      Unsupported:[decimal part](#Decimal_Part_Function)                      |
| 1.10 C1 |  Integral  |                        $\int_0^8 \frac{1}{x-2}dx = \ln{3}$                        |                      [Cauchy principle value](#Cauchy_Principle_Value)                      |
| 1.10 C1 |  Integral  |            $\int_0^3 \frac{1}{(x - 1) ^ {2 / 3}}dx = 3(1 + 2 ^ {1/3})$            |                      [Cauchy principle value](#Cauchy_Principle_Value)                      |
| 1.10 C2 | Inequality |                  $\int_1^\infty \frac{1}{\sqrt{x^3 - 1}} dx < 4$                  |                                                                                              |
| 1.10 C5 |  Integral  |           $\int_0^\frac\pi3 \frac1{\cos \theta}d\theta = \ln(2+\sqrt3)$           |                         [Undetermined ranges](#Undetermined_Ranges)                         |

## Chapter 2: 'Easy' Integrals

### 2.1 Six 'Easy' Warm-Ups (6/6)


|   Type   |                                                  Expression                                                  | Status |
| :------: | :-----------------------------------------------------------------------------------------------------------: | :----: |
| Integral |            $\int_1^\infty \frac{1}{(x+a)\sqrt{x-1}}dx = \frac{\pi}{\sqrt{a+1}}$ <br> for $a > -1$            |  Done  |
| Integral |                $\int_0^\infty \ln{\left(1 + \frac{a^2}{x^2}\right)}dx=\pi a$ <br> for $a > 0$                |  Done  |
| Integral |              $\int_0^\infty \frac{\ln{x}}{x^2 + b^2} dx = \frac{\pi}{2b}\ln{b}$ <br> for $b > 0$              |  Done  |
| Integral |                   $\int_0^\infty \frac{1}{1 + e^{ax}}dx = \frac{\ln{2}}{a}$ <br> for $a>0$                   |  Done  |
| Integral | $\int_{\sqrt{2}}^\infty \frac{1}{x + x^{\sqrt{2}}}dx = (1+\sqrt{2})\ln{(1 + 2 ^{\frac{1}{2}(1 - \sqrt{2})})}$ |  Done  |
| Integral |                             $\int_{-\infty}^{\infty} \frac{1}{\cosh{x}}dx = \pi$                             |  Done  |

### 2.2 A New Trick (5/5)


|   Type   |                                             Expression                                             | Status |
| :------: | :-------------------------------------------------------------------------------------------------: | :----: |
| Integral |  $\int_0^\frac{\pi}{2} \frac{\sqrt{\sin{x}}}{\sqrt{\sin{x}} + \sqrt{\cos{x}}} dx = \frac{\pi}{4}$  |  Done  |
| Integral |                   $\int_0^\pi \frac{x\sin{x}}{1 + \cos^2{x}}dx = \frac{\pi^2}{4}$                   |  Done  |
| Integral | $\int_0^\frac{\pi}{2} \frac{\sin^2{x}}{\sin{x} + \cos{x}}dx = \frac{\sqrt{2}}{4}\ln{(3+2\sqrt{2})}$ |  Done  |
| Integral |                  $\int_0^1 \frac{\ln{(x + 1)}}{x ^ 2 + 1}dx = \frac{\pi}{8}\ln{2}$                  |  Done  |
| Integral |          $\int_0^a \frac{\ln{(x+a)}}{x^2 + a^2}dx = \frac{\pi}{8a}\ln{(2a^2)}$ for $a > 0$          |  Done  |

### 2.3 Two Old New Tricks (6/9)


|   Type   |                                                                                           Expression                                                                                           |                  Status                  |
| :------: | :--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------: | :---------------------------------------: |
| Integral | $\int_0^\infty \frac{1}{\prod_{k=1}^n (x^2 + a_k^2)}dx = \frac{\pi}{2}\sum_{k=1}^n \frac{c_k}{a_k}$ <br> for $c_k = \frac{1}{\prod_{j=1, j\neq k}^n(a_j^2-a_k^2)}$, $a_i\neq a_j$ if $j\neq i$ | [Complex conditions](#Complex_Conditions) |
| Integral |                                                     $\int_0^\infty \frac{1}{x^4 + 2x^2\cosh{(2\alpha)}+1}dx = \frac{\pi}{4\cosh{\alpha}}$                                                     |                   Done                   |
| Integral |                            $\int_0^\infty \frac{1}{x^4 + 2x^2\cos{(2\alpha)}+1}dx = \frac{\pi}{4\left\vert\cos{\alpha}\right\vert}$ <br> for $\cos{\alpha} \neq 0$                            |                   Done                   |
| Integral |                                                $\int_0^\infty \frac{1}{x^4+1}dx = \int_0^\infty \frac{x^2}{x^4 + 1}dx = \frac{\pi \sqrt{2}}{4}$                                                |                   Done                   |
| Integral |                                                                    $\int_0^\infty \frac1{x^4+x^2+1}dx = \frac\pi{2\sqrt3}$                                                                    |                   Done                   |
| Integral |                                                                         $\int_0^\infty \frac1{x^4-x^2+1}dx=\frac\pi2$                                                                         |                   Done                   |
| Integral |                                                                         $\int_0^\infty \frac1{x^4+2x^2+1}dx=\frac\pi4$                                                                         |                   Done                   |
| Integral |                          $\int_0^\pi \frac{\cos{(nx)}-\cos{(n\alpha)}}{\cos{x}-\cos{\alpha}}dx = \pi\frac{\sin{(n\alpha)}}{\sin{\alpha}}$ <br> for $n \in \mathbb{N}$                          |                                          |
| Integral |                                              $\int_0^\infty x^{2n}e^{-x^2}dx = \frac{(2n)!}{4^n n!}(\frac12)\sqrt\pi$ <br> for $n \in \mathbb{N}$                                              |                                          |

### 2.4 Another Old Trick: Euler’s Log-Sine Integral (5/6)


|   Type   |                                                    Expression                                                    |                           Status                           |
| :------: | :---------------------------------------------------------------------------------------------------------------: | :---------------------------------------------------------: |
| Integral | $\int_0^{\frac\pi2}\ln{(a\sin x)}dx = \int_0^{\frac\pi2}\ln{(a\cos x)}dx = \frac\pi2\ln\frac a2$ <br> for $a > 0$ |                            Done                            |
| Integral |                        $\int_0^\frac\pi 2 \ln(\frac{\sin x}x) dx = \frac \pi 2 (1-\ln\pi)$                        |                            Done                            |
| Integral |                              $\int_0^\infty \frac{\ln (x^2+1)}{x^2+1}dx = \pi \ln 2$                              |                            Done                            |
| Integral |                      $\int_0^1 \frac{\ln (x + \frac 1 x )}{x ^ 2 + 1}dx = \frac \pi 2 \ln 2$                      |                            Done                            |
| Integral |                             $\int_0^\infty \frac {\ln x}{1-bx+x^2}dx =0$ for $b < 2$                             | [Overly stringent conditions](#Overly_Stringent_Conditions) |
| Integral |                        $\int_0^1 \frac{1-x}{1+x+x^2} dx = \frac12(\frac\pi{\sqrt3}-\ln3)$                        |                            Done                            |

### 2.5 Challenge Problems (3/4)


|   Type   |                                                         Expression                                                         |                   Status                   |
| :------: | :------------------------------------------------------------------------------------------------------------------------: | :-----------------------------------------: |
| Integral |                                       $\int_0^4 \frac{\ln x}{\sqrt{4x - x^2}}dx =0$                                       |                    Done                    |
| Integral |                               $\int_0^1 \frac1{x^3+1}dx=\frac13(\ln2+\frac{\pi}{\sqrt{3}})$                               |                    Done                    |
| Integral | $\int_0^\infty \frac1{(x^4+1)^{m+1}} dx = \frac{4m-1}{4m}\int_0^\infty \frac1{(x^4+1)^m} dx$ <br> for $m \in \mathbb{N}_+$ | [Undetermined ranges](#Undetermined_Ranges) |
| Integral |                                    $\int_0^\infty \frac{\ln (1+x)}{x\sqrt x}dx = 2\pi$                                    |                    Done                    |

## Chapter 3: Feynman’s Favorite Trick

### 3.1 Leibniz’s Formula (8/10)


|   Type   |                                         Expression                                         | Status |
| :------: | :-----------------------------------------------------------------------------------------: | :----: |
| Integral |              $\int_0^\infty \frac1{x^2+a^2}dx = \frac\pi{2a}$ <br> for $a > 0$              |  Done  |
| Integral |           $\int_0^\infty \frac1{(x^2+a^2)^2}dx = \frac\pi{4a^3}$ <br> for $a > 0$           |  Done  |
| Integral |         $\int_0^\infty \frac1{(x^2+a^2)^3}dx = \frac{3\pi}{16a^5}$ <br> for $a > 0$         |  Done  |
| Integral |                  $\int_{-\infty}^\infty e^{-\frac{x^2}2}dx = \sqrt{2\pi}$                  |  Done  |
| Integral |                   $\int_0^\infty e^{-\frac{-x^2}2}dx = \sqrt{\frac\pi2}$                   |  Done  |
| Integral |     $\int_0^\infty \cos(tx)e^{-\frac{x^2} 2} dx = \sqrt{\frac{\pi} 2}e^{-\frac{t^2}2}$     |  Done  |
| Integral |                  $\int_{-\infty}^\infty e^{-ax^2} dx = \sqrt{\frac\pi a}$                  |  Done  |
| Integral | $\int_{-\infty}^{\infty} e^{-\frac{x^2}2}\cos(s+tx)dx = \sqrt{2\pi}e^{-\frac{t^2}2}\cos s$ |        |
| Integral | $\int_0^\infty \frac{\cos (ax)}{x^2 + b^2}dx = \frac\pi{2b}e^{-ab}$ <br> for $a > 0, b > 0$ |        |
| Integral |                       $\int_0^1 \frac{1}{\sqrt{-\ln x}}dx = \sqrt\pi$                       |  Done  |

### 3.2 An Amazing Integral (1/1)


|   Type   |                            Expression                            | Status |
| :------: | :---------------------------------------------------------------: | :----: |
| Integral | $\int_0^\infty\frac{\sin(ax)}x dx = \frac{\pi}2~\mathrm{sgn}(a) $ |  Done  |

### 3.3 Frullani’s Integral (0/2)


|   Type   |                                                 Expression                                                 |                           Status                           |
| :------: | :---------------------------------------------------------------------------------------------------------: | :---------------------------------------------------------: |
| Integral | $\int_0^\infty \frac{\tan^{-1}(ax)-\tan^{-1}(bx)}x dx = \frac{\pi}2 \ln \frac a b$ <br> for $\frac a b > 0$ | [Overly stringent conditions](#Overly_Stringent_Conditions) |
| Integral |             $\int_0^\infty \frac{e^{-ax} - e^{-bx}}x dx= \ln \frac b a$ <br> for $a > 0, b > 0$             |                                                            |

### 3.4 The Flip-Side of Feynman’s Trick (0/10)


|   Type   |                                                        Expression                                                        |                           Status                           |
| :------: | :-----------------------------------------------------------------------------------------------------------------------: | :---------------------------------------------------------: |
| Integral | $\int_0^\infty \frac{\cos(ax) - \cos (bx)}{x^2} dx = \frac{\pi}{2} (\left\vert b \right\vert - \left\vert a \right\vert)$ |                                                            |
| Integral |            $\int_0^\infty \frac{e^{-pt^2}-e^{-qt^2}}{t^2}dt = \sqrt \pi (\sqrt q - \sqrt p)$ for $p >0, q > 0$            |                                                            |
| Integral |                                 $\int_0^1 \frac{x^a-1}{\ln x} dx = \ln(a+1)$ for $a > -1$                                 | [Overly stringent conditions](#Overly_Stringent_Conditions) |
| Integral |                 $\int_0^1 \frac{x^a-x^b}{\ln x} dx = \frac{\ln(a+1)}{\ln(b+1)}$ <br> for $a > -1, b > -1$                 |                                                            |
| Integral |    $I(t) = \int_0^\infty e^{-tx}\frac{\cos(ax) - \cos (bx)}{x} dx = \ln\sqrt{\frac{t^2+b^2}{t^2+a^2}}$ <br> for $t>0$    |                                                            |
| Integral |    $\int_0^\infty \frac{\cos(ax) - \cos (bx)}{x} dx = \ln\left\vert\frac b a\right\vert$ <br> for $a \neq 0, b \neq0$    |                                                            |
| Integral |                             $\int_0^1 x^a (\ln x)^2 dx = \frac 2{(a+1)^3}$ <br> for $a > -1$                             |                                                            |
| Integral |                    $\int_0^\pi \frac1{a+b\cos x} dx = \frac\pi {\sqrt{a^2-b^2}}$ <br> for $a>b\geq 0$                    |                                                            |
| Integral |              $\int_0^\pi \ln{(a+b\cos x)} dx = \pi\ln\frac{a + \sqrt{a^2-b^2}} {2}$ <br> for $a > b \geq 0$              |                                                            |
| Integral |                   $\int_0^\pi \frac{\ln(1+b\cos x)}{\cos{x}}dx = \pi \sin^{-1} b$ for $-1\leq b \leq 1$                   |                                                            |

### 3.5 Combining Two Tricks (0/6)


|    Type    |                                                                          Expression                                                                          | Status |
| :--------: | :-----------------------------------------------------------------------------------------------------------------------------------------------------------: | :----: |
| Definition |                           $I_n = \int_0^{\frac\pi2} \frac1{(a\cos^2 x + b \sin^2 x)^n} dx$ <br> for $n \in \mathbb{N}_+, a>0, b >0$                           |        |
|  Integral  |           $I_n = -\frac 1 {n-1}(\frac{\partial I_{n-1}}{\partial a} + \frac{\partial I_{n-1}}{\partial b})$ <br> for $n \in \mathbb{N}_+,n \geq 2$           |        |
|  Integral  |                          $I_1 = \int_0^{\frac\pi2} \frac1{a\cos^2 x + b \sin^2 x} dx = \frac{\pi}{2\sqrt{ab}}$ <br> for $a>0, b >0$                          |        |
|  Integral  |             $I_2 = \int_0^{\frac\pi2} \frac1{(a\cos^2 x + b \sin^2 x)^2} dx = \frac{\pi}{4\sqrt{ab}}(\frac 1 a + \frac 1 b)$ <br> for $a>0, b >0$             |        |
|  Integral  | $I_3 = \int_0^{\frac\pi2} \frac1{(a\cos^2 x + b \sin^2 x)^3} dx = \frac{\pi}{16\sqrt{ab}}(\frac 3 {a^2} + \frac 3 {b^2} + \frac 2 {ab})$ <br> for $a>0, b >0$ |        |
|  Integral  |                                     $I_n(y) = \int_0^y \frac 1 {(x^2+a^2)^n}dx$ for $a > 0, y \geq 0, n\in \mathbb{N}_+$                                     |        |
|  Integral  |                         $I_{n+1}(y) = \frac y {2na^2(y^2+a^2)^n} + \frac{2n-1}{2na^2}I_n(y)$ for $a > 0, y \geq 0, n\in \mathbb{N}_+$                         |        |

### 3.6 Uhler’s Integral and Symbolic Integration (0/1)


|   Type   |                     Expression                     | Status |
| :------: | :------------------------------------------------: | :----: |
| Integral | $\int_1 ^ \infty \frac{\ln x}{(1+x)^2} dx = \ln 2$ |        |

### 3.7 The Probability Integral Revisited (0/1)


|   Type   |                                                      Expression                                                      | Status |
| :------: | :------------------------------------------------------------------------------------------------------------------: | :----: |
| Integral | $\int_0^\infty e^{-ax^2-\frac b {x^2}}dx = \frac 1 2 \sqrt{\frac{\pi}{a}}e^{-2\sqrt{ab}}$ <br> for $a > 0, b \geq 0$ |        |

### 3.8 Dini's Integral (0/1)


|   Type   |                                                                          Expression                                                                          | Status |
| :------: | :----------------------------------------------------------------------------------------------------------------------------------------------------------: | :----: |
| Integral | $\int_0^\pi \ln(1-2\alpha\cos x +\alpha^2)dx=\begin{cases}0\quad\quad\quad\ \mathrm{for}~\alpha^2<1\\ \pi\ln\alpha^2\quad\mathrm{for}~\alpha^2>1\end{cases}$ |        |

### 3.10 Challenge Problems (6/10)


|   Type   |                                                                                                                            Expression                                                                                                                            |                           Status                           |
| :------: | :---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------: | :---------------------------------------------------------: |
| Integral |                                                                                   $\int_0^\infty \frac{\ln(1+a^2x^2)}{b^2+x^2}dx = \pi \frac{\ln(1+ab)}b$ <br> for $a > 0, b>0$                                                                                   |                            Done                            |
| Integral |                                                                             $P.V.\int_{-\infty}^{\infty} \frac{\cos (ax)}{b^2-x^2}dx = \pi \frac{\sin(ab)}b$ <br> for $a > 0, b > 0$                                                                             |     [Cauchy principle value](#Cauchy_Principle_Values)     |
| Integral |                                                                             $P.V.\int_{-\infty}^{\infty} \frac{\cos (ax)}{b^4-x^4}dx = \pi \frac{\sin(ab)}b$ <br> for $a > 0, b > 0$                                                                             |     [Cauchy principle value](#Cauchy_Principle_Values)     |
| Integral |                                                                       $P.V.\int_{0}^{\infty} \frac{x\sin (ax)}{x^2-b^2}dx = \frac{\pi\left[e^{-ab}+\sin(ab)\right]}{2b^3}$ <br> for $a > 0$                                                                       |     [Cauchy principle value](#Cauchy_Principle_Values)     |
| Integral | $\int_0^\infty \cos(ax)\frac{\sin(bx)}xdx = \begin{cases} \frac\pi2\quad \mathrm{for}~\left\vert a\right\vert < b, b > 0 \\ 0\quad \mathrm{for}~\left\vert a\right\vert > b, b > 0 \\ \frac\pi4\quad \mathrm{for}~\left\vert a\right\vert = b, b > 0 \end{cases}$ |                            Done                            |
| Integral |                                                                                                             $\int_{-1}^1 \sqrt\frac{1+x}{1-x}dx=\pi$                                                                                                             |                            Done                            |
| Integral |                                                                                                $\int_{-\infty}^{\infty} xe^{-x^2-x}dx = -\frac12\sqrt{\pi\sqrt e}$                                                                                                |                            Done                            |
| Integral |                                                                                               $\int_{-\infty}^{\infty} x^2e^{-x^2-x}dx = \frac34\sqrt{\pi\sqrt e}$                                                                                               |                            Done                            |
| Integral |                                                                          $\int_0^\infty \frac{\sin(mx)}{x(x^2+a^2)^2}dx = \frac{\pi}{2a^4}(1-\frac{2+ma}2e^{-am})$ <br> for $a > 0, m>0$                                                                          |                            Done                            |
| Integral |                                                                                           $\int_0^1 \frac x {\left[ax+b(1-x)\right]^3} = \frac 1 {2a^2b}$ for $ab > 0$                                                                                           | [Overly stringent conditions](#Overly_Stringent_Conditions) |

## Chapter 4: Gamma and Beta Function Integrals

### 4.1 Euler's Gamma Function (3/3)


|    Type    |                          Expression                          | Status |
| :--------: | :----------------------------------------------------------: | :----: |
| Definition | $\Gamma(n) = \int_0^\infty e^{-x}x^{n-1}dx$ <br> for $n > 0$ |  Done  |
|  Integral  | $\Gamma{(n + 1)} = n\Gamma(n)$ <br> for $n \in \mathbb{N}_+$ |  Done  |
|  Integral  |      $\Gamma(n) = (n-1)!$ <br> for $n \in \mathbb{N}_+$      |  Done  |
|  Integral  |       $\int_0^\infty e ^{-x^3} dx = \Gamma(\frac 4 3)$       |  Done  |

### 4.2 Wallis’ Integral and the Beta Function (12/17)


|    Type    |                                                                                  Expression                                                                                  | Status |
| :--------: | :--------------------------------------------------------------------------------------------------------------------------------------------------------------------------: | :----: |
| Definition |                                                  $\Beta(m, n) = \int_0 ^ 1 x^{m-1}(1-x)^{n-1} dx $ <br> for $m >0 , n > 0$                                                  |  Done  |
|  Integral  |                                                       $\Gamma(m) = 2\int_0^\infty e^{-x^2}x^{2m-1}dx$ <br> for $m > 0$                                                       |        |
|  Integral  | $\Gamma(m)\Gamma(n) = \left[2\int_0^\infty e^{-r^2}r^{2(m+n)-1}dr\right]\left[2\int_0^{\frac\pi2} \cos^{2m-1}\theta \sin^{2n-1}\theta d\theta\right]$ <br> for $m > 0, n >0$ |        |
|  Integral  |                    $\Gamma(m)\Gamma(n) = \Gamma(m+n)\left[2\int_0^{\frac\pi2} \cos^{2m-1}\theta \sin^{2n-1}\theta d\theta\right]$ <br> for $m > 0, n >0$                    |        |
|  Integral  |                                                 $\Beta(m,n) = \frac{\Gamma(m)\Gamma(n)}{\Gamma(m+n)}$ <br> for $m > 0, n >0$                                                 |        |
|  Integral  |                                                  $I(n) = \int_0^1 (x-x^2)^n dx = \frac{(n!)^2}{(2n+1)!}$ <br> for $n > -1$                                                  |  Done  |
|  Integral  |                                                                     $(\frac 1 2)! = \frac 1 2 \sqrt \pi$                                                                     |  Done  |
|  Integral  |                                                             $\int_0^\infty e^{-x}\sqrt x dx = \frac 1 2\sqrt\pi$                                                             |  Done  |
|  Integral  |                                                                $\int_0^1 \sqrt{-\ln x} dx =\frac 1 2\sqrt\pi$                                                                |  Done  |
|  Integral  |                                                            $\int_0^\infty \frac {e^{-x}}{\sqrt x} dx = \sqrt\pi$                                                            |  Done  |
|  Integral  |                                                                  $\Gamma(\frac12) = (-\frac12)! = \sqrt\pi$                                                                  |  Done  |
|  Integral  |                    $\int_0^{\frac{\pi}{2}} \sqrt{\sin x} dx=\frac{\Gamma(\frac34)\Gamma(\frac12)}{2\Gamma(\frac54)}=\int_0^{\frac{\pi}2}\sqrt{\cos x}dx$                    |  Done  |
|  Integral  |                                           $\int_0^\frac\pi 2 \frac 1{\sqrt{\sin x\cos x}}dx = \frac{\Gamma^2(\frac14)}{2\sqrt\pi}$                                           |  Done  |
|  Integral  |                    $\int_0^{\frac{\pi}{2}} \frac 1 {\sqrt{\sin x}} dx=\frac{\Gamma^2(\frac14)}{2\sqrt{2\pi}}=\int_0^{\frac{\pi}2}\frac1{\sqrt{\cos x}}dx$                    |  Done  |
|  Integral  |                                       $\int_0^\infty \frac{y^{m-1}}{1+y}dy = \Beta(m, 1-m) = \Gamma(m)\Gamma(1-m)$ <br> for $0 < m<1$                                       |  Done  |
|  Integral  |                                                      $\Gamma(m)\Gamma(1-m) = \frac\pi{\sin(m\pi)}$ <br> for $0 < m <1$                                                      |  Done  |
|  Integral  |                                                        $z!(z+\frac12)! = 2^{-2z-1}\sqrt\pi(2z+1)!$ <br> for $z > -1$                                                        |  Done  |
|  Integral  |                                                          $z!(z-\frac12)! = 2^{-2z}\sqrt\pi(2z)!$ for $z > -\frac12$                                                          |        |

### 4.3 Double Integration Reversal (0/11)


|   Type   |                                                             Expression                                                             | Status |
| :------: | :--------------------------------------------------------------------------------------------------------------------------------: | :----: |
| Integral |          $\int_0^\infty \frac{\sin(bx)}{x^p}dx =\frac{b^{p-1}\pi}{2\Gamma(p)\sin\frac{p\pi}2}$ <br> for $b > 0, 0 < p <2$          |        |
| Integral |           $\int_0^\infty \frac{\sin x^q}{x^q}dx =\frac{\pi}{2q\Gamma(2-\frac1q)\sin\frac{\pi}{2q}}$ <br> for $q>\frac12$           |        |
| Integral |       $\int_0^\infty \frac{\sin x^q}{x^q}dx =\frac{\pi}{2(q-1)(-\frac1q)!\sin\frac{\pi}{2q}}$ <br> for $q>\frac12, q\neq 1$       |        |
| Integral |                     $(-\frac1q)! = \frac{\frac\pi q}{(\frac1q)!\sin\frac\pi q}$ <br> for $q>\frac12, q\neq 1$                     |        |
| Integral |   $\int_0^\infty \frac{\sin x^q}{x^q}dx =\frac{(\frac1q)!}{\frac1q}(\frac1{q-1})\cos\frac\pi{2q}$ <br> for $q>\frac12, q\neq 1$   |        |
| Integral |      $\int_0^\infty \frac{\sin x^q}{x^q}dx = \frac{\Gamma(\frac1q)}{q-1}\cos\frac\pi{2q}$ <br> for $q >1$ or $\frac12 < q <1$      |        |
| Integral |          $\int_0^\infty \frac{\cos(bx)}{x^p}dx =\frac{b^{p-1}\pi}{2\Gamma(p)\cos\frac{p\pi}2}$ <br> for $b > 0, 0 < p <1$          |        |
| Integral |              $\int_0^\infty\sin(bx^k)dx = \frac{\Gamma(\frac1k)\sin\frac\pi{2k}}{kb^\frac1k}$ <br> for $b > 0, k > 1$              |        |
| Integral |              $\int_0^\infty\cos(bx^k)dx = \frac{\Gamma(\frac1k)\cos\frac\pi{2k}}{kb^\frac1k}$ <br> for $b > 0, k > 1$              |        |
| Integral |               $\int_0^\infty \cos(bx)\int_0^ce^{-xy}dydx = \int_0^c\frac y{b^2+y^2}dy$ <br> for $b \neq 0 , c\geq0$               |        |
| Integral |                  $\int_0^\infty \frac{1-e^{-cx}}x\cos(bx)dx = \frac12 \ln\frac{b^2+c^2}{b^2}$ <br> for $b \neq 0$                  |        |
| Integral | $\int_0^\infty \frac{e^{-rx}\cos(px) - e^{-sx}\cos(qx)}xdx=\frac12\ln\frac{q^2+s^2}{p^2+r^2}$ <br> for $(q^2 + s^2)(p^2+r^2)\neq0$ |        |

### 4.5 Challenge Problems (0/9)


|    Type    |                                                                    Expression                                                                    |                     Status                     |
| :--------: | :-----------------------------------------------------------------------------------------------------------------------------------------------: | :---------------------------------------------: |
| Definition |                                                $I(n) = \int_0^1 (1-\sqrt x)^n dx$ <br> for $n>-1$                                                |                                                |
|  Integral  |                                                   $I(n)= \frac2{(n+1)(n+2)}$ <br> for $n > -1$                                                   | [Incomplete conditions](#Incomplete_Conditions) |
|  Integral  |                                                                $I(9) = \frac1{55}$                                                                |                                                |
|  Integral  |                                  $\int_0^1 x^m\ln^x x dx = {(-1)}^n\frac{n!}{(m+1)^{n+1}}$ <br> for $m>-1, n>-1$                                  | [Incomplete conditions](#Incomplete_Conditions) |
|  Integral  |                                   $\int_0^1 x^a\int_0^{1-x}y^bdydx=\frac{a!b!}{(a+b+2)!}$ <br> for $a > 0, b>0$                                   |                                                |
|  Integral  |                       $\int_0^\infty \frac{\sin x}{\sqrt x} dx = \int_0^\infty \frac{\cos x}{\sqrt x} dx = \sqrt\frac\pi 2$                       |                                                |
|  Integral  |                                $\int_0^\infty \sin x^2 dx =\int_0^\infty \cos x^2 dx = \frac{\sqrt\frac{\pi}{2}}2$                                |                                                |
|  Integral  |                                 $\int_0^\infty \sin(bx) \frac{e^{-cx}}x = \tan^{-1}\frac b c$ <br> for $c \neq 0$                                 |                                                |
|  Integral  | $\int_0^\infty \frac{x^a}{(1+x^b)^c}dx = \frac{\Gamma(\frac{1+a}b)\Gamma(c-\frac{1+a}b)}{b\Gamma(c)}$ <br> for $a > -1, b > 0, c > \frac{1+a}{b}$ |                                                |
|  Integral  |     $\int_0^\infty \frac{\sin x^2}{\sqrt x} dx = \int_0^\infty \frac{\cos x^2}{\sqrt x} dx = \frac{\pi}{4\Gamma(\frac34)}\cos(\frac{3\pi}8)$     |                                                |

## Chapter 5: Using Power Series to Evaluate Integrals

### 5.1 Catalan’s Constant (3/4)


|    Type    |                                                            Expression                                                            | Status |
| :--------: | :------------------------------------------------------------------------------------------------------------------------------: | :----: |
| Definition |                                            $G = \sum_{k=0}^\infty \frac{1}{(2k+1)^2}$                                            |  Done  |
|  Integral  |                                              $\int_0^1 \frac{\tan^{-1} x }x dx =G$                                              |  Done  |
|  Integral  |                                             $\int_1^\infty \frac{\ln x}{x^2+1}dx =G$                                             |  Done  |
|  Integral  |                                  $\int_0^\infty \frac{\ln (x+1)}{x^2+1}dx = \frac\pi 4\ln 2+G$                                  |  Done  |
|  Integral  | $ \int_0^\pi \frac{\theta\sin \theta}{a + b\cos^2 \theta}d\theta = \frac\pi{\sqrt ab}\tan^{-1}\sqrt\frac ba $ <br> for $a > b>0$ |        |

### 5.2 Power Series for the Log Function (2/7)


|   Type   |                                 Expression                                 | Status |
| :------: | :-------------------------------------------------------------------------: | :----: |
| Integral |             $\int_0^1 \frac{\ln (1+x)}x dx = \frac{\pi^2}{12}$             |  Done  |
| Integral |             $\int_0^1 \frac{\ln (1-x)}x dx = -\frac{\pi^2}{6}$             |        |
| Integral |        $\int_0^1 \frac 1x \ln (\frac{1-x}{1+x})^2 dx =\frac{\pi^2}2$        |        |
| Integral |      $\int_0^{\frac{\pi}2} \cot x \ln (\sec x) dx = \frac{\pi^2}{24}$      |  Done  |
| Integral |       $\int_0^1\ln(1+x)\ln(1-x)dx=(\ln 2)^2 -2\ln 2+2 -\frac{\pi^2}6$       |        |
| Integral |          $\int_0^1 \frac{(\ln x)^2}{1+x^2} dx = \frac{\pi^3}{16}$          |        |
| Integral | $\int_0^\frac{\pi}2 \left[\ln(\tan \theta)\right]^2 d\theta =\frac{\pi^3}8$ |        |

### 5.3 Zeta Function Integrals (3/6)


|    Type    |                                                               Expression                                                               |                     Status                     |
| :--------: | :-------------------------------------------------------------------------------------------------------------------------------------: | :---------------------------------------------: |
| Definition |                                               $\zeta(s) =\sum_{k=1}^\infty \frac{1}{k^s}$                                               |                      Done                      |
|  Integral  |                    $\int_0^1 \int_0^1 \frac{x^ay^a}{1-xy}dxdy = \sum_{n=1}^\infty \frac 1{(n+a)^2}$ <br> for $a>-1$                    |                      Done                      |
|  Integral  | $\int_0^1 \int_0^1 \frac{(xy)^a\left[\ln (xy)\right]^{s-2}}{1-xy}dxdy =(-1)^s(s-1)!\sum_{n=1}^\infty \frac1{(n+a)^s}$ <br> for $s\geq2$ | [Incomplete conditions](#Incomplete_Conditions) |
|  Integral  |                      $\zeta(s) = \frac{(-1)^s}{(s-1)!}\int_0^1\int_0^1\frac{\left[\ln(xy)\right]^{s-2}}{1-xy}dxdy$                      |                      Done                      |
|  Integral  |                                       $\int_0^\infty \frac{x^{s-1}}{e^x-1}dx =\Gamma(s)\zeta(s)$                                       |                      Done                      |
|  Integral  |                                     $\sum_{k=1}^\infty \frac{(-1)^{k-1}}{k^s}=\zeta(s)(1-2^{1-s})$                                     |                                                |
|  Integral  |                                 $\int_0^\infty \frac{x^{s-1}}{e^x+1}dx = (1-2^{1-s})\Gamma(s)\zeta(s)$                                 |                                                |

### 5.4 Euler’s Constant and Related Integrals (0/6)


|    Type    |                                               Expression                                               | Status |
| :--------: | :----------------------------------------------------------------------------------------------------: | :----: |
| Definition |                  $\gamma(n) = \sum_{k=1}^n (\frac1k -\ln n)$ for $n \in \mathbb{N}_+$                  |        |
| Definition |                             $\gamma = \lim_{n\rightarrow\infty}\gamma(n)$                             |        |
|  Integral  |                  $\gamma = \int_0^1 \frac{1-e^{-u}}udu-\int_0^\infty\frac{e^{-u}}udu$                  |        |
|  Integral  |                                 $\int_0^\infty e^{-x}\ln x dx =\gamma$                                 |        |
|  Integral  |                                    $\int_0^1 \ln(-\ln x)dx=-\gamma$                                    |        |
|  Integral  | $\int_{-\infty}^\infty e^{-\alpha e^x}+e^{-\alpha e^{-x}}-1dx=-\gamma-\ln\alpha$ <br> for $\alpha > 0$ |        |
|  Integral  |         $\int_0^\infty \frac{e^{-x^a}-e^{-x^b}}xdx=\gamma\frac{a-b}{ab}$ <br> for $a >0, b>0$         |        |
|  Integral  |                   $\int_0^\infty e^{-x^2}\ln x dx = -\frac14\sqrt\pi(\gamma+2\ln 2)$                   |        |

### 5.5 Challenge Problems (0/11)


|    Type    |                                                   Expression                                                   |                       Status                       |
| :--------: | :------------------------------------------------------------------------------------------------------------: | :------------------------------------------------: |
| Definition |            $I(m,n) = \int_0^1 \frac{1-x^m}{1-x^n}dx$ <br> for $m\in\mathbb{N}_+, n\in\mathbb{N}_+$            |                                                    |
|  Integral  |       $I(m,n) = m\sum_{k=0}^\infty \frac1{(kn+1)(kn+m+1)}$ <br> for $m\in\mathbb{N}_+, n\in\mathbb{N}_+$       |                                                    |
|  Integral  |                              $\int_1^\infty \frac{\left\{x\right\}}x dx=1-\gamma$                              | Unsupported:[decimal part](#Decimal_Part_Function) |
|  Integral  |                      $\zeta(3) = \frac32 -3\int_1^\infty \frac{\left\{x\right\}}{x^4}dx$                      | Unsupported:[decimal part](#Decimal_Part_Function) |
|  Integral  |                         $\lim_{a\rightarrow 1} (\frac1{1-a}+\frac1{\ln a}) = \frac12$                         |                                                    |
|  Integral  |                  $2\sum_{k=1}^\infty \frac{(-1)^{k-1}}{k^2} = \sum_{k=1}^\infty \frac1{k^2}$                  |                                                    |
|  Integral  |                                   $\int_0^1 \frac{\ln^2 (1-x)}x =2\zeta(3)$                                   |                                                    |
|  Integral  |                   $\int_0^1\frac{(-\ln x)^p}{1-x}dx =\Gamma(p+1)\zeta(p+1)$ <br> for $p > 0$                   |                                                    |
|  Integral  | $\int_0^1\int_0^1...\int_0^1\frac1{1-\prod_{k=1}^n x_k}dx_1dx_2...dx_n =\zeta(n)$ <br> for $n\in \mathbb{N}_+$ |     [Complex conditions](#Complex_Conditions)     |
|  Integral  |                             $\int_0^\infty \ln\frac{e^x+1}{e^x-1}dx=\frac{\pi^2}4$                             |                                                    |
|  Integral  |                           $\int_0^\infty e^{-x}\ln^2 x dx = \gamma^2+\frac{\pi^2}6$                           |                                                    |
|  Integral  |                              $\gamma = \int_0^1 \frac{1-e^{-x}-e^{-\frac1x}}xdx$                              |                                                    |

## Chapter 6: Seven Not-So-Easy Integrals (7/11)


| Section |    Type    |                                                     Expression                                                     | Status |
| :-----: | :--------: | :-----------------------------------------------------------------------------------------------------------------: | :----: |
|   6.1   |  Integral  |                            $\int_0^1 x^{cx^a}dx = \sum_{k=0}^\infty \frac{c^k}{(a+1)^k}$                            |  Done  |
|   6.1   |  Integral  |                          $\int_0^1 x^x dx = \sum_{k=0}^\infty \frac{(-1)^k}{(k+1)^{k+1}}$                          |  Done  |
|   6.1   |  Integral  |                           $\int_0^1 x^{-x} dx = \sum_{k=0}^\infty \frac{1}{(k+1)^{k+1}}$                           |  Done  |
|   6.1   |  Integral  |                        $\int_0^1 x^{x^2} dx = \sum_{k=0}^\infty \frac{(-1)^k}{(2k+1)^{k+1}}$                        |  Done  |
|   6.1   |  Integral  |                      $\int_0^1 x^{\sqrt x}dx = \sum_{k=0}^\infty (-1)^k (\frac 2 {k+2})^{k+1}$                      |  Done  |
|   6.2   |  Integral  |               $\int_0^1 \frac{\tan^{-1} (\sqrt{2+x^2})}{(1+x^2)\sqrt{2+x^2}}dx = \frac {5\pi^2}{96}$               |  Done  |
|   6.3   |  Integral  |                    $\int_0^\frac{\pi}2 \cos^{-1}(\frac{\cos x}{1+2\cos x})dx=\frac{5\pi^2}{24}$                    |  Done  |
|   6.4   |  Integral  |               $\int_0^\infty \int_x^\infty \int_x^\infty \cos(t^2-u^2)dtdudx = \frac12\sqrt\frac\pi2$               |        |
|   6.5   |  Integral  | $\frac1{\pi^3}\int_0^\pi\int_0^\pi\int_0^\pi\frac1{1-\cos u \cos v \cos w}dudvdw =\frac{\Gamma^4(\frac14)}{4\pi^3}$ |        |
| 6.7 C1 |  Integral  |                         $\int_0^\frac{\pi}2\cos^{-1}(\frac1{1+2\cos x})dx = \frac{\pi^2}6$                         |        |
| 6.7 C2 | Definition |            $f(x) = \frac x {x^n + 1} - \frac 1 {\sum_{k=0}^{n-1} x^k}$ for $n\in \mathbb{N}_+, n \geq 3$            |        |
| 6.7 C2 |  Integral  |                                              $\int_0^\infty f(x)dx=0$                                              |        |

## Chapter 7: Using $\sqrt {-1}$ to Evaluate Integrals

### 7.1 Euler's Formula (0/1)


|   Type   |                             Expression                             | Status |
| :------: | :----------------------------------------------------------------: | :----: |
| IntegraL | $\int_0^\infty \sin(bx)e^{-xy}dx=\frac b{y^2+b^2}$ <br> for $y >0$ |        |

### 7.2 The Fresnel Integrals (0/3)


|   Type   |                        Expression                        | Status |
| :------: | :------------------------------------------------------: | :----: |
| Integral |   $\int_0^\infty \cos x^2 dx =\frac12\sqrt\frac\pi 2$   |        |
| Integral |   $\int_0^\infty \sin x^2 dx =\frac12\sqrt\frac\pi 2$   |        |
| Integral | $\int_0^\infty e^{ix^2}dx =\frac12\sqrt{\frac\pi2}(1+i)$ |        |

### 7.3 $\zeta(3)$ and More Log-Sine Integrals (0/3)


|   Type   |                                                                                        Expression                                                                                        | Status |
| :------: | :--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------: | :----: |
| Integral |                                                          $\int_0^\frac\pi2x\ln(\sin x)dx =\frac7{16}\zeta(3)-\frac{\pi^2}8\ln2$                                                          |        |
| Integral | $\int_0^\frac\pi2\ln^2(a\sin\theta)d\theta=\int_0^\frac\pi2\ln^2(a\cos\theta)d\theta=\frac{\pi^3}{24}+\frac\pi6\left[\ln^2 (\frac2a) -2\ln(\frac2a)\ln (\frac a2)\right]$ <br> for $a>0$ |        |
| Integral |              $\int_0^\frac\pi2\ln(a\sin\theta)\ln(a\cos\theta)d\theta=\frac\pi6\left[\ln^2 (\frac2a) -2\ln(\frac2a)\ln (\frac a2)\right]-\frac{\pi^3}{48}$ <br> for $a >0$              |        |

### 7.4 $\zeta(2)$, At Last! (0/1)


|   Type   |         Expression         | Status |
| :------: | :------------------------: | :----: |
| Integral | $\zeta(2) = \frac{\pi^2}6$ |        |

### 7.5 The Probability Integral *Again* (0/1)


|   Type   |                                             Expression                                             | Status |
| :------: | :------------------------------------------------------------------------------------------------: | :----: |
| Integral | $\int_0^\infty \frac{\cos x}{\sqrt x}dx = \int_0^\infty \frac{\sin x}{\sqrt x}dx = \sqrt\frac\pi2$ |        |

### 7.6 Beyond Dirichlet’s Integral (0/5)


|   Type   |                                                                 Expression                                                                 | Status |
| :------: | :-----------------------------------------------------------------------------------------------------------------------------------------: | :----: |
| Integral |                                              $\int_0^\infty (\frac{\sin x}x)^2 dx =\frac\pi2$                                              |        |
| Integral |                                             $\int_0^\infty (\frac{\sin x}x)^3 dx =\frac{3\pi}8$                                             |        |
| Integral |                     $\int_0^\infty \frac{\sin^{2n-1} x}xdx =\frac\pi{2^{2n-1}}\binom{2n-2}{n-1}$ for $n\in\mathbb{N}_+$                     |        |
| Integral |                  $\int_0^\infty \frac{\sin^{2n-1} x\cos x}xdx =\frac\pi{2^{2n}n}\binom{2n-2}{n-1}$ for $n\in\mathbb{N}_+$                  |        |
| Integral | $\int_0^\infty \frac{\sin^{2n} x}{x^2}dx=\int_0^\infty \frac{\sin^{2n-1} x}xdx =\frac\pi{2^{2n-1}}\binom{2n-2}{n-1}$ for $n\in\mathbb{N}_+$ |        |

### 7.7 Dirichlet Meets the Gamma Function (0/4)


|   Type   |                                                                                 Expression                                                                                 | Status |
| :------: | :-------------------------------------------------------------------------------------------------------------------------------------------------------------------------: | :----: |
| Integral |   $\int_0^\infty \frac{\sin^p x}{x^q}dx = \frac{p!}{(q-1)!}\int_0^\infty \frac{u^{q-2}}{\prod_{k=1}^{\frac p 2}\left[u^2+(2k)^2\right]}du$ <br> for $ p $ is even, $q>0$   |        |
| Integral | $\int_0^\infty \frac{\sin^p x}{x^q}dx = \frac{p!}{(q-1)!}\int_0^\infty \frac{u^{q-1}}{\prod_{k=0}^{\frac {p-1} 2}\left[u^2+(2k+1)^2\right]}du$ <br> for $ p $ is odd, $q>0$ |        |
| Integral |                                                               $\int_0^\infty (\frac{\sin x}x)^4dx =\frac\pi3$                                                               |        |
| Integral |                                                           $\int_0^\infty \frac{\sin^3 x}{x^2}dx =\frac{3\ln 3}4$                                                           |        |

### 7.8 Fourier Transforms and Energy Integrals (0/5)


|   Type   |                                                                    Expression                                                                    | Status |
| :------: | :-----------------------------------------------------------------------------------------------------------------------------------------------: | :----: |
| Integral |              $\frac1{2\pi}\int_{-\infty}^{\infty}\frac{\left\vert e^{-ix a}-e^{-ix b}\right\vert ^2}{x^2}dx = b -a$ <br> for $b >a$              |        |
| Integral | $\int_{-\infty}^{\infty} \frac{1-\cos(ax)\cos(bx)}{x^2}dx - \int_{-\infty}^{\infty} \frac{\sin(ax)sin(bx)}{x^2}dx = \pi\left\vert b-a\right\vert$ |        |
| Integral |                                               $\int_{-\infty}^{\infty}\frac{1-\cos u}{u^2}du =\pi$                                               |        |
| Integral |           $\int_{-\infty}^{\infty} \frac{1-\cos(ax)\cos(bx)}{x^2}dx + \int_{-\infty}^{\infty} \frac{\sin(ax)sin(bx)}{x^2}dx = \pi(b+a)$           |        |
| Integral |        $\int_{-\infty}^{\infty} \frac{\sin(ax)sin(bx)}{x^2}dx = \pi\min(\left\vert a\right\vert,\left\vert b\right\vert)~\mathrm{sgn}(ab)$        |        |

### 7.9 ‘Weird’ Integrals from Radio Engineering

- 7.9.1

- [ ]
  $$
  \int_0^\infty \frac{\sin(t\omega)}\omega d\omega =
  \begin{cases}
  \frac{\pi}2\quad\mathrm{for}~t >0\\
  -\frac{\pi}2\ \mathrm{for}~t <0
  \end{cases}
  $$

- 7.9.2

- [ ]
  $$
  \int_{-\infty}^\infty \frac{\sin(t\omega)}\omega d\omega =
  \begin{cases}
  \pi\quad\mathrm{for}~t>0\\
  -\pi\ \mathrm{for}~t<0
  \end{cases}
  $$

- 7.9.3

- [ ]  $\int_{-\infty}^{\infty} \frac{e^{i\omega t}}\omega d\omega =i\pi~\mathrm{sgn}(t)$

- 7.9.4

- [ ]  $u(t)=\frac{1+\mathrm{sgn}(t)}2$ (Definition)

- 7.9.5

- [ ]  $\int_{-\infty}^\infty e^{i\omega t} d\omega = \pi\frac{d}{dt}~\mathrm{sgn}(t)$

- 7.9.6

- [ ]  $\int_{-\infty}^\infty e^{i\omega t} d\omega = 2\pi\delta(t)$

- 7.9.7

- [ ]  $\mathrm{sgn}(t)\leftrightarrow\frac2{i\omega}$

- 7.9.8

- [ ]  $\delta(t)\leftrightarrow1$

- 7.9.9

- [ ]  $u(t)\leftrightarrow\int_{-\infty}^\infty \frac12e^{-i\omega t} dt +\frac1{i\omega}$

- 7.9.10

- [ ]  $\int_{-\infty}^\infty e^{it\omega } dt = 2\pi\delta(\omega)$

- 7.9.11

- [ ]  $\int_{-\infty}^\infty e^{-i\omega t} dt = 2\pi\delta(\omega)$

- 7.9.12

- [ ]  $u(t)\leftrightarrow\pi\delta(\omega)+\frac1{i\omega}$

- 7.9.13

- [ ]  $\cos(\omega_0t)\leftrightarrow\pi\delta(\omega-\omega_0)+\pi\delta(\omega+\omega_0)$

- 7.9.14

- [ ]  $\int_{-\infty}^{\infty} \delta(t-a)\phi(t) dt =\phi(a)$

- 7.9.15

- [ ]  $g(t) \leftrightarrow G(\omega) $ for $ G(t) \leftrightarrow2\pi g(-\omega)$

- 7.9.16

- [ ]  $f(t) \leftrightarrow F(\omega) $ for $ f(at) \leftrightarrow\frac1a F(\frac\omega a)$

- 7.9.17

- [ ]  $m(t)g(t)\leftrightarrow\frac1{2\pi}\int_{-\infty}^{\infty}G(u)M(\omega-u)du$

#### 7.10 Causality and Hilbert Transform Integrals

- 7.10.1

- [ ]  $g(t)=g_e(t)+g_o(t)$

- 7.10.2

- [ ]  $g(-t) = g_e(-t) + g_o(-t) = g_e(t) - g_o(t)$

- 7.10.3

- [ ]  $g_e(t) = \frac12 \left[g(t)+g(-t)\right]$

- 7.10.4

- [ ]  $g_o(t) = \frac12 \left[g(t)-g(-t)\right]$

- 7.10.5

- [ ]  $g_e(t) = g_o(t)~\mathrm{sgn}(t)$

- 7.10.6

- [ ]  $g_o(t) = g_e(t)~\mathrm{sgn}(t)$

- 7.10.7

- [ ]  $G_e(\omega) = R(\omega)$

- 7.10.8

- [ ]  $G_o(\omega) =iX(\omega)$

- 7.10.9

- [ ]  $R(\omega) = \frac1{2\pi}iX(\omega) * \frac2{i\omega} =\frac1\pi X(\omega)*\frac1\omega$

- 7.10.10

- [ ]  $X(\omega) = -\frac1\pi R(\omega)*\frac1\omega$

- 7.10.11

- [ ]  $R(\omega) = \frac1\pi\int_{-\infty}^{\infty}\frac{X(u)}{\omega-u}du$
- [ ]  $X(\omega) = -\frac1\pi\int_{-\infty}^{\infty}\frac{X(u)}{\omega-u}du$

- 7.10.12

- [ ]  $\overline{x(t)}=\frac1\pi \int_{-\infty}^{\infty}\frac{x(u)}{t-u}du$

- 7.10.13

- [ ]  $\int_{-\infty}^{\infty}\frac{1}{t-u}du=0$

- 7.10.14

- [ ]
  $$
  \pi(t)=
  \begin{cases}
  1\quad\mathrm{for}~-\frac12<t<\frac12\\
  0\quad\mathrm{otherwise}
  \end{cases}
  $$

- 7.10.15

- [ ]  $\Pi(\omega) = \frac{e^{i\omega \frac12}-e^{-i\omega\frac12}}{i\omega}=\frac{i2\sin\frac\omega2}{i\omega}=\frac{\sin\frac\omega2}{\frac\omega2}$ for $-\infty < \omega < \infty$

- 7.10.16

- [ ]  $\frac{\sin\frac t2}{\frac t2} \leftrightarrow2\pi~\pi(-\omega)=2\pi~\pi(\omega)$

- 7.10.17

- [ ]
  $$
  \frac{\sin t}t \leftrightarrow 
  \begin{cases}
  \pi\quad\mathrm{for}~-1<\omega<1\\
  0\quad\mathrm{otherwise}
  \end{cases}
  $$

- 7.10.18

- [ ]
  $$
  \frac{\sin t}{2t} = \frac12 \frac{\sin(t)}t\leftrightarrow R(\omega) =
  \begin{cases}
  \frac\pi2\quad\mathrm{for}~-1<\omega<1\\
  0\quad\mathrm{otherwise}
  \end{cases}
  $$

- 7.10.19

- [ ]  $X(\omega) = \frac12 \ln(\left\vert\frac{1-\omega}{1+\omega}\right\vert)$ for $-\infty < \omega < \infty$

- 7.10.20

- [ ]  $\int_0^\infty \ln^2(\left\vert\frac{1-x}{1+x}\right\vert)=\pi^2$

#### 7.11 Challenge Problems

- C7.1

- [ ]  $\int_0^\infty (\frac{\sin x}x)^5dx =\frac{115}{384}\pi$
- [ ]  $\int_0^\infty (\frac{\sin x}x)^6dx =\frac{11}{40}\pi$
- [ ]  $\int_0^\infty (\frac{\sin x}x)^7dx =\frac{5887}{23040}\pi$

- C7.2

- [ ]  $F(x) = \int_x^\infty\int_x^\infty \sin(t^2-u^2)dtdu =0$

- C7.3

- [ ]  $\mathrm{convergence}~\int_{-\infty}^{\infty} \frac{1}{1-ix^3}dx$

- C7.4

- [ ]  $\int_1^\infty \frac{\left\{x\right\}}{x^3} dx =1-\frac{\pi^2}{12}$

- C7.5

- [ ]  $I(a) = \int_0^\infty \frac{\sin^2(ax)}{x^2} dx$ (Definition)
- [ ]  $I(a)= \frac\pi2\left\vert a\right\vert$

- C7.7

- [ ]

  $$
  f(t)=
  \begin{cases}
  e^{-at}\ \mathrm{for}~0\leq t\leq m \\
  0\quad\ \mathrm{otherwise}
  \end{cases}\quad\mathrm{for}~a > 0,m>0
  $$
- [ ]  $\int_{-\infty}^\infty \frac{\cos(mx)}{x^2+a^2}dx = \frac\pi a e^{-ma}$ for $a >0, m >0$

- C7.8

- [ ]  $\frac1{t^2+1} \leftrightarrow \pi e^{-\left\vert \omega\right\vert}$
- [ ]  $\frac t{t^2+1} \leftrightarrow -i\pi e ^{-\left\vert\omega\right\vert}~\mathrm{sgn}(\omega)$
- [ ]  $\frac12\delta(t)+i\frac1{2\pi t}\leftrightarrow u(\omega)$
- [ ]  $\int_t^\infty \frac{e^{-u}}udu \leftrightarrow \frac{\ln(1+i\omega)}{i\omega}$

- C7.9

- [ ]  $X(\omega) = -\frac{2\omega}\pi \int_0^\infty \frac{R(u)}{\omega^2-u^2}du$

- C7.10

- [ ]  $\frac1{2\pi}\int_{-\infty}^{\infty} \left\vert X(\omega)\right\vert^2d\omega < \infty$
- [ ]  $y(t)=x(t)*h(t)=\int_{-\infty}^\infty x(u)h(t-u)du$
- [ ]  $\int_{-\infty}^\infty \left\vert h(t)\right\vert dt < \infty$
- [ ]  $\frac1{2\pi}\int_{-\infty}^{\infty} \left\vert Y(\omega)\right\vert^2d\omega < \infty$

- C7.11

- [ ]  $\overline{\sin(\omega_0t)} = -\cos(\omega_0t)$ for $\omega_0>0$
- [ ]  $\overline{\cos(\omega_0t)} = \sin(\omega_0t)$ for $\omega_0>0$

## Chapter 8: Contour Integration

### 8.3 Functions of a Complex Variable (0/1)

|   Type   |                                      Expression                                       | Status |
| :------: |:-------------------------------------------------------------------------------------:|:------:|
| Integral | $\int_0^{2\pi} e^{\cos\theta}d\theta = 2\pi \sum_{m=0}^\infty \frac{1}{2^{2m}(m!)^2}$ |        |

### 8.6 Cauchy’s First Integral Theorem (0/5)

|   Type   |                                           Expression                                            | Status |
| :------: |:-----------------------------------------------------------------------------------------------:|:------:|
| Integral |                          $\int_0^\infty \frac{\cos x - e^{-x}}x dx =0$                          |        |
| Integral |          $P.V.\int_{-\infty}^\infty \frac{1}{ax^2+bx+c}dx = 0$ for $a\neq 0, b^2>4ac$           |        |
| Integral | $P.V.\int_{-\infty}^\infty \frac{e^{ax}}{1-e^{x}}dx = \frac{\pi}{\tan(a\pi)}$ <br> for $0<a<1$  |        |
| Integral |  $\int_0^\infty \frac{\cos(x)}{x+a} = \int_0^\infty \frac{xe^{-x}}{x^2+a^2}dx$ <br> for $a>0$   |        |
| Integral | $\int_0^\infty \frac{\sin(x)}{x+a} = a\int_0^\infty a\frac{e^{-x}}{x^2+a^2}dx$ <br> for $a > 0$ |        |

### 8.7 Cauchy’s Second Integral Theorem (0/6)

|   Type   |                                                                    Expression                                                                     | Status |
| :------: |:-------------------------------------------------------------------------------------------------------------------------------------------------:|:------:|
| Integral |                        $\int_{\infty}^{\infty} \frac{1}{ax^2+bx+c}=\frac{2\pi}{\sqrt{4ac-b^2}}$ <br> for $a\neq0, b^2<4ac$                        |        |
| Integral | $\int_0^\infty \frac{x^m}{x^n+1}dx = \frac{\frac{\pi}n}{\sin\left[ (m+1)\frac\pi n\right]}$ <br> for $m \in \mathbb{N},n\in\mathbb{N}, n-m\geq 2$ |        |
| Integral |                                  $\int_0^\infty \frac{x^{a-1}}{x+1}dx = \frac{\pi}{\sin(a\pi)}$ <br> for $0<a<1$                                  |        |
| Integral |                             $\int_{-\infty}^\infty \frac{e^{ax}}{1+e^x} dx = \frac{\pi}{\sin(a\pi)}$ <br> for $0<a<1$                             |        |
| Integral |                              $\int_{-\infty}^\infty \frac{1}{(1+x)x^a} dx = \frac{\pi}{\sin(a\pi)}$ <br> for $0<a<1$                              |        |
| Integral |                                $\int_0^{2\pi} \frac{1}{a+\sin^2 \theta}=\frac{2\pi}{\sqrt{a(a+1)}}$ <br> for $a>0$                                |        |

### 8.8 Singularities and the Residue Theorem (0/3)

|   Type   |                                                       Expression                                                       | Status |
| :------: |:----------------------------------------------------------------------------------------------------------------------:|:------:|
| Integral |  $\int_0^{2\pi} \cos^k \theta d\theta = \frac{2\pi}{2^k} \frac{k!}{\left[(\frac k2)!\right]^2}$ <br> for $k$ is even   |        |
| Integral |           $\int_0^{2\pi} \frac{1}{(1+k\cos\theta)^2}d\theta = \frac{2\pi}{(1-k^2)^\frac32}$ <br> for $k <1$            |        |
| Integral |$\int_0^\infty \frac{\ln x}{(x+a)^2 +b^2}dx = \frac 1b \tan^{-1} (\frac ba) \ln(\sqrt{a^2+b^2})$ <br> for $a\geq 0,b>0$ |        |

### 8.10 Challenge Problems

|   Type   |                                              Expression                                              | Status |
| :------: |:----------------------------------------------------------------------------------------------------:|:------:|
| Integral | $\int_0^\infty \frac{\sin(mx)}{x(x^2+a^2)}dx = \frac\pi2(\frac{1-e^{-am}}{a^2})$ <br> for $a>0, m>0$ |        |
| Integral |      $\int_0^{2\pi} \frac{1}{1-2a\cos\theta +a^2} d\theta= \frac{2\pi}{1-a^2}$ <br> for $0<a<1$      |        |
- [ ]  $\int_{-\infty}^{\infty} \frac{\cos x}{(x+a)^2 + b ^2} dx = \frac{\pi}b e^{-b}\cos a$ for $a >0, b>0$
- [ ]  $\int_{-\infty}^{\infty} \frac{\sin x}{(x+a)^2 + b ^2} dx = -\frac{\pi}b e^{-b}\sin a$ for $a >0, b>0$
- [ ]  $\int_{-\infty}^\infty \frac{\cos x}{(x^2+a^2)(x^2+b^2)}dx = \frac\pi{a^2-b^2}(\frac{e^{-b}}b-\frac{e^{-a}}a)$ for $a>b>0$
- [ ]  $\int_{-\infty}^{\infty} \frac{\cos (ax)}{(x^2+b^2)^2} dx = \frac{\pi}{4b^3} (1+ab)e^{-ab}$ for $a >0, b>0$

- C8.4

- [ ]  $\int_0^\infty \frac{x^k}{(x^2+1)^2}dx = \frac{\pi(1-k)}{4\cos \frac{k\pi}2}$ for $-1<k<3$

- C8.5

- [ ]  $\int_{-\infty}^{\infty} \frac{\cos (mx)}{ax^2+bx+c}dx = -2\pi\frac{\cos\frac{mb}{2a}\sin\frac{m\sqrt{b^2-4ac}}{2a}}{\sqrt{b^2-4ac}}$ for $b^2\geq 4ac$

- C8.6

- [ ]  $\int_0^{\infty} \frac{x^p}{(x+1)(x+2)}dx=(2^p-1)\frac{\pi}{\sin(px)}$ for $-1<p<1$
- [ ]  $\int_0^{\infty} \frac{x^\frac12}{(x+1)(x+2)}dx=(\sqrt2-1)\pi$

- C8.7

- [ ]  $\int_0^\infty \frac{e^{\cos x }\sin(\sin x)}xdx=\frac\pi2(e-1)$

- C8.8

- [ ]  $\int_{-\infty}^{\infty} \frac{x^2}{(x^2+a^2)^3}dx=\frac\pi{8a^3}$ for $a>0$

## Unsolved Problems

Here shows the problems to be solved.

### Unsupported Functions

Some functions haven't been supported yet.

<h4 id=Cauchy_Principle_Value>Cauchy Principle Value</h4>

Some improper integrals may not be convergent. However, sometimes we can calculate the Cauchy principle value of the integral. It is somewhat like a mistake that a beginner will make.

<h4 id=Decimal_Part_Function>Decimal Part Function</h4>

Suppose that $x=3.14$, and then $\left\{x\right\}$ gets $0.14$. It's easy to see that $0\leq\left\{x\right\}<1$ for $x\in\mathbb{R}$. Notice that when $x$ is negative, the result of $\left\{x\right\}$ seems strange. For example, if $x=-3.14$, then $\left\{x\right\}$ gets $0.86$, for $-3.14 = -4 + 0.86$.

### Conditions

Some integral-related equations only hold under specific conditions.

<h4 id=Complex_Conditions>Complex Conditions</h4>

Some conditions are too difficult to express right now.

<h4 id=Incomplete_Conditions>Incomplete Conditions</h4>

We have shown that some propositions hold, but did not fully specify the conditions of them. In other words, the proof is not rigorous.

<h4 id=Overly_Stringent_Conditions>Overly Stringent Conditions</h4>

We have shown that some propositions hold, but in fact, the conditions of them can be weakened.

### Unsolved Expressions

Not all expressions can be solved easily.

<h4 id=Undetermined_Ranges>Undetermined Ranges</h4>

It is tough to calculate the ranges of some expressions. Even worse, some operations can not be performed if it is uncertain whether the denominator may be equal to zero.
