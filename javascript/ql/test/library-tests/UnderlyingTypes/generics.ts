import * as express from 'express';

type Box1<T> = {
    value: T;
    other: string;
};
function t1(b: Box1<express.Request>) {
    b.value; // $ hasUnderlyingType='express'.Request
    b.other;
}

interface Box2<T> {
    value: T;
    other: string;
}
function t2(b: Box2<express.Request>) {
    b.value; // $ hasUnderlyingType='express'.Request
    b.other;
}

class Box3<T> {
    value: T;
    other: string;
}
function t3(b: Box3<express.Request>) {
    b.value; // $ hasUnderlyingType='express'.Request
    b.other;
}

abstract class Box4<T> {
    abstract getValue(): T;
    abstract getOther(): string;
}
function t4(b: Box4<express.Request>) {
    b.getValue(); // $ hasUnderlyingType='express'.Request
    b.getOther();
}

interface Box5<T> {
    value: T & { blah: string };
    other: string;
};
interface Box5Sub<T> extends Box5<T> { }
function t5(b: Box5<express.Request>, sub: Box5Sub<express.Request>) {
    b.value; // $ hasUnderlyingType='express'.Request
    b.other;

    sub.value; // $ hasUnderlyingType='express'.Request
}

type Box6<T> = (p: T) => void;
function t6(): Box6<express.Request> {
    return function (p) { }  // $ hasUnderlyingType='express'.Request
}

interface Box7<T> {
    p1: {
        p2: {
            p3: T
        }
    }
}
function t7(b: Box7<express.Request>) {
    b.p1;
    b.p1.p2;
    b.p1.p2.p3; // $ hasUnderlyingType='express'.Request
}

interface Box8Step<T> {
    p2: T;
}
interface Box8<T> {
    p1: Box8Step<{ p3: T }>
}
function t8(b: Box8<express.Request>) {
    b.p1;
    b.p1.p2;
    b.p1.p2.p3; // $ hasUnderlyingType='express'.Request
}

interface Box9Base<T> {
    p1: { p2: { p3: T } }
}
interface Box9<T> extends Box9Base<T> {
}
function t9(b: Box9<express.Request>) {
    b.p1;
    b.p1.p2;
    b.p1.p2.p3; // $ hasUnderlyingType='express'.Request
}

interface Box10Base<T> {
    p1: { p2: T }
}
interface Box10<T> extends Box10Base<{ p3: T }> {
}
function t10(b: Box10<express.Request>) {
    b.p1;
    b.p1.p2;
    b.p1.p2.p3; // $ hasUnderlyingType='express'.Request
}

interface Box11Base1<T> {
    p1: T
}
interface Box11Base2<T> extends Box11Base1<{ p2: T }> {
}
interface Box11<T> extends Box11Base2<{ p3: T }> {
}
type Alias11 = Box11<express.Request>;
function t11(b: Box11<express.Request>, alias: Alias11) {
    b.p1;
    b.p1.p2;
    b.p1.p2.p3; // $ hasUnderlyingType='express'.Request

    alias.p1;
    alias.p1.p2;
    alias.p1.p2.p3; // $ hasUnderlyingType='express'.Request
}

class Box12Base<T> {
    p1: T;
}
class Box12<T> extends Box12Base<T> {
}
function t12(b: Box12<express.Request>) {
    b.p1; // $ hasUnderlyingType='express'.Request
}
