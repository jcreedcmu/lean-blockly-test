import type { ReactNode } from 'react';

type ModalProps = {
  onClose: () => void;
  className?: string;
  bodyClassName?: string;
  children: ReactNode;
};

export function Modal({ onClose, className, bodyClassName, children }: ModalProps) {
  return (
    <div className="modal-backdrop" onClick={onClose}>
      <div className={`modal${className ? ` ${className}` : ''}`} onClick={(e) => e.stopPropagation()}>
        <button
          className="modal-close"
          onClick={onClose}
          title="Close"
        >&times;</button>
        <div className={`modal-body${bodyClassName ? ` ${bodyClassName}` : ''}`}>
          {children}
        </div>
      </div>
    </div>
  );
}
