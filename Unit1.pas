unit Unit1;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, Forms, Controls, Graphics, Dialogs, ExtCtrls,
  StdCtrls, ComCtrls, Grids, LCLIntf, LCLType, Math;

type
  TPt2 = record
    X, Y: real;
  end;

  TPt3 = record
    X, Y, Z: real;
  end;

  TPt2Array = array of TPt2;
  TPt2Levels = array of TPt2Array;
  TPt3Row = array of TPt3;
  TPt3Grid = array of TPt3Row;

  { TForm1 }

  TForm1 = class(TForm)
    PageControl1: TPageControl;
    TabBezier: TTabSheet;
    TabChaikin: TTabSheet;
    TabSurface: TTabSheet;

    PaintBoxBezier: TPaintBox;
    EditN: TEdit;
    EditT: TEdit;
    ButtonBezierBuild: TButton;
    ButtonBezierStep: TButton;
    ButtonBezierResetStep: TButton;
    ButtonBezierClear: TButton;
    LabelN: TLabel;
    LabelT: TLabel;
    LabelBezierInfo: TLabel;

    PaintBoxChaikin: TPaintBox;
    EditIters: TEdit;
    ButtonChaikinRefine: TButton;
    ButtonChaikinClear: TButton;
    LabelIters: TLabel;
    LabelChaikinInfo: TLabel;

    PaintBoxSurface: TPaintBox;
    EditRows: TEdit;
    EditCols: TEdit;
    EditSurfN: TEdit;
    StringGridZ: TStringGrid;
    ButtonSurfaceGrid: TButton;
    ButtonSurfaceRandom: TButton;
    ButtonSurfaceBuild: TButton;
    LabelRows: TLabel;
    LabelCols: TLabel;
    LabelSurfN: TLabel;

    procedure FormCreate(Sender: TObject);

    procedure PaintBoxBezierPaint(Sender: TObject);
    procedure PaintBoxBezierMouseDown(Sender: TObject; Button: TMouseButton;
      Shift: TShiftState; X, Y: Integer);
    procedure ButtonBezierBuildClick(Sender: TObject);
    procedure ButtonBezierStepClick(Sender: TObject);
    procedure ButtonBezierResetStepClick(Sender: TObject);
    procedure ButtonBezierClearClick(Sender: TObject);

    procedure PaintBoxChaikinPaint(Sender: TObject);
    procedure PaintBoxChaikinMouseDown(Sender: TObject; Button: TMouseButton;
      Shift: TShiftState; X, Y: Integer);
    procedure ButtonChaikinRefineClick(Sender: TObject);
    procedure ButtonChaikinClearClick(Sender: TObject);

    procedure PaintBoxSurfacePaint(Sender: TObject);
    procedure ButtonSurfaceGridClick(Sender: TObject);
    procedure ButtonSurfaceRandomClick(Sender: TObject);
    procedure ButtonSurfaceBuildClick(Sender: TObject);
  private
    { Вкладка "Кривая Безье" }
    BezierPoints: TPt2Array;
    BezierCurvePts: TPt2Array;
    BezierHasCurve: Boolean;
    BezierLevels: TPt2Levels;
    BezierStepLevel: Integer;

    { Вкладка "Кривая Чайкина" }
    ChaikinOriginal: TPt2Array;
    ChaikinCurrent: TPt2Array;
    ChaikinIterDone: Integer;

    { Вкладка "Поверхность Безье" }
    SurfRows, SurfCols: Integer;
    SurfCtrl: TPt3Grid;
    SurfMesh: TPt3Grid;
    SurfHasMesh: Boolean;
    SurfHasCtrl: Boolean;
  public
  end;

var
  Form1: TForm1;

implementation

{$R *.lfm}

{ ------------------------------------------------------------------- }
{ Общие вспомогательные функции                                       }
{ ------------------------------------------------------------------- }

function BinCoeff(n, i: Integer): real;
var
  k: Integer;
  r: real;
begin
  r := 1;
  for k := 0 to i - 1 do
    r := r * (n - k) / (k + 1);
  Result := r;
end;

// Базисная функция (полином Бернштейна) степени n, номер i, параметр t
function Bernstein(n, i: Integer; t: real): real;
begin
  Result := BinCoeff(n, i) * Power(t, i) * Power(1 - t, n - i);
end;

function Lerp2(const a, b: TPt2; t: real): TPt2;
begin
  Result.X := a.X + t * (b.X - a.X);
  Result.Y := a.Y + t * (b.Y - a.Y);
end;

// ---------------------------------------------------------------------
// Геометрическое построение кривой Безье методом де Кастельжо.
// Возвращает все промежуточные уровни уточнения: levels[0] - исходные
// контрольные точки, levels[k] - множество точек после k шагов линейной
// интерполяции по ломаной предыдущего уровня, levels[High] - единственная
// точка, лежащая на кривой при заданном t (именно так на рис. 1-9
// методического пособия строится точка кривой Безье).
// ---------------------------------------------------------------------
procedure DeCasteljauLevels(const pts: TPt2Array; t: real; out levels: TPt2Levels);
var
  i, lvl, n: Integer;
begin
  n := Length(pts);
  SetLength(levels, n);
  SetLength(levels[0], n);
  for i := 0 to n - 1 do
    levels[0][i] := pts[i];
  for lvl := 1 to n - 1 do
  begin
    SetLength(levels[lvl], Length(levels[lvl - 1]) - 1);
    for i := 0 to High(levels[lvl]) do
      levels[lvl][i] := Lerp2(levels[lvl - 1][i], levels[lvl - 1][i + 1], t);
  end;
end;

function DeCasteljauPoint(const pts: TPt2Array; t: real): TPt2;
var
  cur: TPt2Array;
  i, k: Integer;
begin
  SetLength(cur, Length(pts));
  for i := 0 to High(pts) do
    cur[i] := pts[i];
  for k := 1 to Length(pts) - 1 do
  begin
    for i := 0 to Length(cur) - 2 do
      cur[i] := Lerp2(cur[i], cur[i + 1], t);
    SetLength(cur, Length(cur) - 1);
  end;
  Result := cur[0];
end;

// ---------------------------------------------------------------------
// Один шаг "углового отсечения" Чайкина: для каждого звена P[i]P[i+1]
// исходной ломаной строятся две новые точки Qi (ближе к P[i], в
// соотношении 1/4 от P[i+1]) и Ri (ближе к P[i+1], в соотношении 1/4 от
// P[i]). Новый уточнённый полигон из 2*(n-1) точек сходится к гладкой
// кривой при повторном применении процедуры.
// ---------------------------------------------------------------------
function ChaikinSubdivide(const pts: TPt2Array): TPt2Array;
var
  i, n, cnt: Integer;
begin
  n := Length(pts);
  if n < 2 then
  begin
    SetLength(Result, n);
    for i := 0 to n - 1 do
      Result[i] := pts[i];
    Exit;
  end;
  SetLength(Result, 2 * (n - 1));
  cnt := 0;
  for i := 0 to n - 2 do
  begin
    Result[cnt].X := 0.75 * pts[i].X + 0.25 * pts[i + 1].X;
    Result[cnt].Y := 0.75 * pts[i].Y + 0.25 * pts[i + 1].Y;
    Inc(cnt);
    Result[cnt].X := 0.25 * pts[i].X + 0.75 * pts[i + 1].X;
    Result[cnt].Y := 0.25 * pts[i].Y + 0.75 * pts[i + 1].Y;
    Inc(cnt);
  end;
end;

// ---------------------------------------------------------------------
// Точка поверхности Безье p(u,v) по формуле (5) методического пособия:
// p(u,v) = sum_i sum_j P[i,j] * B_i,n(u) * B_j,m(v), где n=nRows-1,
// m=nCols-1 - степени полинома по каждому направлению, B - полиномы
// Бернштейна (базисные функции кривой Безье).
// ---------------------------------------------------------------------
function SurfacePoint(const ctrl: TPt3Grid; nRows, nCols: Integer; u, v: real): TPt3;
var
  i, j: Integer;
  bu, bv, w: real;
begin
  Result.X := 0; Result.Y := 0; Result.Z := 0;
  for i := 0 to nRows - 1 do
  begin
    bu := Bernstein(nRows - 1, i, u);
    for j := 0 to nCols - 1 do
    begin
      bv := Bernstein(nCols - 1, j, v);
      w := bu * bv;
      Result.X := Result.X + ctrl[i][j].X * w;
      Result.Y := Result.Y + ctrl[i][j].Y * w;
      Result.Z := Result.Z + ctrl[i][j].Z * w;
    end;
  end;
end;

// Кавальерная (косоугольная) проекция точки трёхмерного пространства на
// плоскость холста: ось Z откладывается под углом 30° к горизонтали.
function Project3D(const p: TPt3; originX, originY: Integer; scale: real): TPoint;
const
  ang = 30 * pi / 180;
begin
  Result.X := originX + round(scale * (p.X + p.Z * cos(ang)));
  Result.Y := originY - round(scale * (p.Y + p.Z * sin(ang)));
end;

{ ------------------------------------------------------------------- }
{ TForm1                                                               }
{ ------------------------------------------------------------------- }

procedure TForm1.FormCreate(Sender: TObject);
begin
  Randomize;
  EditN.Text := '40';
  EditT.Text := '0.5';
  EditIters.Text := '3';
  EditRows.Text := '4';
  EditCols.Text := '4';
  EditSurfN.Text := '16';

  SetLength(BezierPoints, 0);
  SetLength(BezierCurvePts, 0);
  BezierHasCurve := False;
  BezierStepLevel := 0;

  SetLength(ChaikinOriginal, 0);
  SetLength(ChaikinCurrent, 0);
  ChaikinIterDone := 0;

  SurfHasMesh := False;
  SurfHasCtrl := False;

  ButtonSurfaceGridClick(nil);
end;

{ ---------------------- Вкладка "Кривая Безье" ---------------------- }

procedure TForm1.PaintBoxBezierMouseDown(Sender: TObject; Button: TMouseButton;
  Shift: TShiftState; X, Y: Integer);
var
  n: Integer;
begin
  if Button <> mbLeft then Exit;
  n := Length(BezierPoints);
  SetLength(BezierPoints, n + 1);
  BezierPoints[n].X := X;
  BezierPoints[n].Y := Y;
  BezierHasCurve := False;
  BezierStepLevel := 0;
  SetLength(BezierLevels, 0);
  PaintBoxBezier.Invalidate;
end;

procedure TForm1.PaintBoxBezierPaint(Sender: TObject);
var
  cnv: TCanvas;
  i, lvl: Integer;
  colors: array[0..5] of TColor;
begin
  cnv := PaintBoxBezier.Canvas;
  cnv.Brush.Color := RGB(255, 255, 255);
  cnv.FillRect(PaintBoxBezier.ClientRect);

  // исходный контрольный полигон (пункт 6а: точки исходного полигона)
  cnv.Pen.Style := psDash;
  cnv.Pen.Color := RGB(180, 180, 180);
  cnv.Pen.Width := 1;
  for i := 0 to Length(BezierPoints) - 2 do
    cnv.Line(round(BezierPoints[i].X), round(BezierPoints[i].Y),
             round(BezierPoints[i + 1].X), round(BezierPoints[i + 1].Y));

  cnv.Brush.Style := bsSolid;
  cnv.Brush.Color := RGB(60, 60, 60);
  cnv.Pen.Style := psSolid;
  for i := 0 to High(BezierPoints) do
    cnv.Ellipse(round(BezierPoints[i].X) - 3, round(BezierPoints[i].Y) - 3,
                round(BezierPoints[i].X) + 3, round(BezierPoints[i].Y) + 3);

  // готовая кривая (после "Построить")
  if BezierHasCurve then
  begin
    cnv.Pen.Color := RGB(0, 90, 200);
    cnv.Pen.Width := 2;
    for i := 0 to Length(BezierCurvePts) - 2 do
      cnv.Line(round(BezierCurvePts[i].X), round(BezierCurvePts[i].Y),
               round(BezierCurvePts[i + 1].X), round(BezierCurvePts[i + 1].Y));
    cnv.Pen.Width := 1;
  end;

  // пошаговая визуализация де Кастельжо (пункт 1б: промежуточные вершины)
  colors[0] := RGB(0, 150, 0);
  colors[1] := RGB(200, 120, 0);
  colors[2] := RGB(200, 0, 150);
  colors[3] := RGB(0, 150, 200);
  colors[4] := RGB(150, 0, 0);
  colors[5] := RGB(100, 100, 0);
  if (BezierStepLevel > 0) and (Length(BezierLevels) > 0) then
  begin
    for lvl := 1 to Min(BezierStepLevel, High(BezierLevels)) do
    begin
      cnv.Pen.Color := colors[(lvl - 1) mod 6];
      cnv.Pen.Width := 2;
      for i := 0 to Length(BezierLevels[lvl]) - 2 do
        cnv.Line(round(BezierLevels[lvl][i].X), round(BezierLevels[lvl][i].Y),
                 round(BezierLevels[lvl][i + 1].X), round(BezierLevels[lvl][i + 1].Y));
      cnv.Brush.Color := colors[(lvl - 1) mod 6];
      for i := 0 to High(BezierLevels[lvl]) do
        cnv.Ellipse(round(BezierLevels[lvl][i].X) - 3, round(BezierLevels[lvl][i].Y) - 3,
                    round(BezierLevels[lvl][i].X) + 3, round(BezierLevels[lvl][i].Y) + 3);
    end;
    cnv.Pen.Width := 1;
    // если дошли до последнего уровня - это и есть точка на кривой
    if BezierStepLevel >= High(BezierLevels) then
    begin
      cnv.Brush.Color := RGB(220, 0, 0);
      i := 0;
      cnv.Ellipse(round(BezierLevels[High(BezierLevels)][0].X) - 5,
                  round(BezierLevels[High(BezierLevels)][0].Y) - 5,
                  round(BezierLevels[High(BezierLevels)][0].X) + 5,
                  round(BezierLevels[High(BezierLevels)][0].Y) + 5);
    end;
  end;
end;

procedure TForm1.ButtonBezierBuildClick(Sender: TObject);
var
  n, i: Integer;
  t: real;
begin
  if Length(BezierPoints) < 2 then
  begin
    ShowMessage('Задайте не менее двух контрольных точек кликами на поле.');
    Exit;
  end;
  if not TryStrToInt(Trim(EditN.Text), n) or (n < 1) then
    n := 40;

  SetLength(BezierCurvePts, n + 1);
  for i := 0 to n do
  begin
    t := i / n;
    BezierCurvePts[i] := DeCasteljauPoint(BezierPoints, t);
  end;
  BezierHasCurve := True;
  PaintBoxBezier.Invalidate;
end;

procedure TForm1.ButtonBezierStepClick(Sender: TObject);
var
  t: real;
  fs: TFormatSettings;
begin
  if Length(BezierPoints) < 2 then
  begin
    ShowMessage('Задайте не менее двух контрольных точек кликами на поле.');
    Exit;
  end;
  fs := DefaultFormatSettings;
  fs.DecimalSeparator := '.';
  if not TryStrToFloat(Trim(EditT.Text), t, fs) then
    t := 0.5;

  if Length(BezierLevels) = 0 then
    DeCasteljauLevels(BezierPoints, t, BezierLevels);

  if BezierStepLevel < High(BezierLevels) then
    Inc(BezierStepLevel)
  else
    ShowMessage('Построение завершено: получена точка на кривой при t=' + FloatToStr(t) + '.');

  PaintBoxBezier.Invalidate;
end;

procedure TForm1.ButtonBezierResetStepClick(Sender: TObject);
begin
  BezierStepLevel := 0;
  SetLength(BezierLevels, 0);
  PaintBoxBezier.Invalidate;
end;

procedure TForm1.ButtonBezierClearClick(Sender: TObject);
begin
  SetLength(BezierPoints, 0);
  SetLength(BezierCurvePts, 0);
  SetLength(BezierLevels, 0);
  BezierHasCurve := False;
  BezierStepLevel := 0;
  PaintBoxBezier.Invalidate;
end;

{ --------------------- Вкладка "Кривая Чайкина" ---------------------- }

procedure TForm1.PaintBoxChaikinMouseDown(Sender: TObject; Button: TMouseButton;
  Shift: TShiftState; X, Y: Integer);
var
  n: Integer;
begin
  if Button <> mbLeft then Exit;
  n := Length(ChaikinOriginal);
  SetLength(ChaikinOriginal, n + 1);
  ChaikinOriginal[n].X := X;
  ChaikinOriginal[n].Y := Y;
  SetLength(ChaikinCurrent, n + 1);
  ChaikinCurrent[n] := ChaikinOriginal[n];
  ChaikinIterDone := 0;
  PaintBoxChaikin.Invalidate;
end;

procedure TForm1.PaintBoxChaikinPaint(Sender: TObject);
var
  cnv: TCanvas;
  i: Integer;
begin
  cnv := PaintBoxChaikin.Canvas;
  cnv.Brush.Color := RGB(255, 255, 255);
  cnv.FillRect(PaintBoxChaikin.ClientRect);

  // исходный контрольный полигон (пункт 6а)
  cnv.Pen.Style := psDash;
  cnv.Pen.Color := RGB(180, 180, 180);
  cnv.Pen.Width := 1;
  for i := 0 to Length(ChaikinOriginal) - 2 do
    cnv.Line(round(ChaikinOriginal[i].X), round(ChaikinOriginal[i].Y),
             round(ChaikinOriginal[i + 1].X), round(ChaikinOriginal[i + 1].Y));
  cnv.Brush.Style := bsSolid;
  cnv.Brush.Color := RGB(60, 60, 60);
  cnv.Pen.Style := psSolid;
  for i := 0 to High(ChaikinOriginal) do
    cnv.Ellipse(round(ChaikinOriginal[i].X) - 3, round(ChaikinOriginal[i].Y) - 3,
                round(ChaikinOriginal[i].X) + 3, round(ChaikinOriginal[i].Y) + 3);

  // уточнённый полигон после N итераций (пункт 6б: вершины уточнённого
  // контрольного полигона); при больших N визуально сходится к гладкой кривой
  cnv.Pen.Color := RGB(0, 150, 0);
  cnv.Pen.Width := 2;
  for i := 0 to Length(ChaikinCurrent) - 2 do
    cnv.Line(round(ChaikinCurrent[i].X), round(ChaikinCurrent[i].Y),
             round(ChaikinCurrent[i + 1].X), round(ChaikinCurrent[i + 1].Y));
  cnv.Pen.Width := 1;
  if ChaikinIterDone > 0 then
  begin
    cnv.Brush.Color := RGB(0, 150, 0);
    for i := 0 to High(ChaikinCurrent) do
      cnv.Ellipse(round(ChaikinCurrent[i].X) - 2, round(ChaikinCurrent[i].Y) - 2,
                  round(ChaikinCurrent[i].X) + 2, round(ChaikinCurrent[i].Y) + 2);
  end;

  LabelChaikinInfo.Caption := 'Итераций выполнено: ' + IntToStr(ChaikinIterDone) +
    ' | точек в полигоне: ' + IntToStr(Length(ChaikinCurrent));
end;

procedure TForm1.ButtonChaikinRefineClick(Sender: TObject);
var
  target, k: Integer;
  tmp: TPt2Array;
begin
  if Length(ChaikinOriginal) < 2 then
  begin
    ShowMessage('Задайте не менее двух точек исходного полигона кликами на поле.');
    Exit;
  end;
  if not TryStrToInt(Trim(EditIters.Text), target) or (target < 0) then
    target := 3;

  SetLength(tmp, Length(ChaikinOriginal));
  for k := 0 to High(ChaikinOriginal) do
    tmp[k] := ChaikinOriginal[k];
  for k := 1 to target do
    tmp := ChaikinSubdivide(tmp);

  ChaikinCurrent := tmp;
  ChaikinIterDone := target;
  PaintBoxChaikin.Invalidate;
end;

procedure TForm1.ButtonChaikinClearClick(Sender: TObject);
begin
  SetLength(ChaikinOriginal, 0);
  SetLength(ChaikinCurrent, 0);
  ChaikinIterDone := 0;
  PaintBoxChaikin.Invalidate;
end;

{ ------------------- Вкладка "Поверхность Безье" ------------------- }

procedure TForm1.ButtonSurfaceGridClick(Sender: TObject);
var
  r, c, i, j: Integer;
begin
  if not TryStrToInt(Trim(EditRows.Text), r) or (r < 2) then r := 4;
  if not TryStrToInt(Trim(EditCols.Text), c) or (c < 2) then c := 4;
  SurfRows := r;
  SurfCols := c;

  StringGridZ.RowCount := r;
  StringGridZ.ColCount := c;
  for i := 0 to r - 1 do
    for j := 0 to c - 1 do
      if StringGridZ.Cells[j, i] = '' then
        StringGridZ.Cells[j, i] := '0';

  SurfHasMesh := False;
  SurfHasCtrl := False;
  PaintBoxSurface.Invalidate;
end;

procedure TForm1.ButtonSurfaceRandomClick(Sender: TObject);
var
  i, j: Integer;
begin
  ButtonSurfaceGridClick(nil);
  for i := 0 to SurfRows - 1 do
    for j := 0 to SurfCols - 1 do
      StringGridZ.Cells[j, i] := IntToStr(Random(140) - 70);
  PaintBoxSurface.Invalidate;
end;

procedure TForm1.ButtonSurfaceBuildClick(Sender: TObject);
var
  i, j, nSteps: Integer;
  u, v, z, spacing: real;
  fs: TFormatSettings;
begin
  if not TryStrToInt(Trim(EditRows.Text), SurfRows) or (SurfRows < 2) then SurfRows := 4;
  if not TryStrToInt(Trim(EditCols.Text), SurfCols) or (SurfCols < 2) then SurfCols := 4;
  if not TryStrToInt(Trim(EditSurfN.Text), nSteps) or (nSteps < 1) then nSteps := 16;

  fs := DefaultFormatSettings;
  fs.DecimalSeparator := '.';
  spacing := 40;

  // считываем массив исходных контрольных вершин: X,Y - регулярная сетка,
  // Z - значения, введённые пользователем в таблице (пункт 4а: произвольное
  // количество исходных вершин задаётся размером строк/столбцов)
  SetLength(SurfCtrl, SurfRows);
  for i := 0 to SurfRows - 1 do
  begin
    SetLength(SurfCtrl[i], SurfCols);
    for j := 0 to SurfCols - 1 do
    begin
      if not TryStrToFloat(Trim(StringGridZ.Cells[j, i]), z, fs) then
        z := 0;
      SurfCtrl[i][j].X := j * spacing;
      SurfCtrl[i][j].Y := i * spacing;
      SurfCtrl[i][j].Z := z;
    end;
  end;
  SurfHasCtrl := True;

  // сэмплируем поверхность по формуле (5) с выбранным параметром разбиения
  // (пункт 4б: количество шагов по каждому из направлений u,v)
  SetLength(SurfMesh, nSteps + 1);
  for i := 0 to nSteps do
  begin
    SetLength(SurfMesh[i], nSteps + 1);
    u := i / nSteps;
    for j := 0 to nSteps do
    begin
      v := j / nSteps;
      SurfMesh[i][j] := SurfacePoint(SurfCtrl, SurfRows, SurfCols, u, v);
    end;
  end;
  SurfHasMesh := True;
  PaintBoxSurface.Invalidate;
end;

procedure TForm1.PaintBoxSurfacePaint(Sender: TObject);
var
  cnv: TCanvas;
  i, j: Integer;
  originX, originY: Integer;
  p1, p2: TPoint;
begin
  cnv := PaintBoxSurface.Canvas;
  cnv.Brush.Color := RGB(255, 255, 255);
  cnv.FillRect(PaintBoxSurface.ClientRect);

  originX := 70;
  originY := PaintBoxSurface.Height - 40;

  // исходный контрольный полигон (сетка вершин) - пункт 6а
  if SurfHasCtrl then
  begin
    cnv.Pen.Style := psDash;
    cnv.Pen.Color := RGB(180, 180, 180);
    cnv.Pen.Width := 1;
    for i := 0 to SurfRows - 1 do
      for j := 0 to SurfCols - 2 do
      begin
        p1 := Project3D(SurfCtrl[i][j], originX, originY, 1.0);
        p2 := Project3D(SurfCtrl[i][j + 1], originX, originY, 1.0);
        cnv.Line(p1.X, p1.Y, p2.X, p2.Y);
      end;
    for j := 0 to SurfCols - 1 do
      for i := 0 to SurfRows - 2 do
      begin
        p1 := Project3D(SurfCtrl[i][j], originX, originY, 1.0);
        p2 := Project3D(SurfCtrl[i + 1][j], originX, originY, 1.0);
        cnv.Line(p1.X, p1.Y, p2.X, p2.Y);
      end;
    cnv.Brush.Style := bsSolid;
    cnv.Brush.Color := RGB(60, 60, 60);
    cnv.Pen.Style := psSolid;
    for i := 0 to SurfRows - 1 do
      for j := 0 to SurfCols - 1 do
      begin
        p1 := Project3D(SurfCtrl[i][j], originX, originY, 1.0);
        cnv.Ellipse(p1.X - 3, p1.Y - 3, p1.X + 3, p1.Y + 3);
      end;
  end;

  // сглаженная сетка поверхности Безье (каркасный рисунок) - пункт 6б
  if SurfHasMesh then
  begin
    cnv.Pen.Style := psSolid;
    cnv.Pen.Color := RGB(0, 90, 200);
    cnv.Pen.Width := 1;
    for i := 0 to High(SurfMesh) do
      for j := 0 to High(SurfMesh[i]) - 1 do
      begin
        p1 := Project3D(SurfMesh[i][j], originX, originY, 1.0);
        p2 := Project3D(SurfMesh[i][j + 1], originX, originY, 1.0);
        cnv.Line(p1.X, p1.Y, p2.X, p2.Y);
      end;
    for j := 0 to High(SurfMesh[0]) do
      for i := 0 to High(SurfMesh) - 1 do
      begin
        p1 := Project3D(SurfMesh[i][j], originX, originY, 1.0);
        p2 := Project3D(SurfMesh[i + 1][j], originX, originY, 1.0);
        cnv.Line(p1.X, p1.Y, p2.X, p2.Y);
      end;
  end;
end;

end.
